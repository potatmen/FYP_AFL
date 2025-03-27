/*
  Copyright 2015 Google LLC All rights reserved.

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at:

    http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
*/

/*
   american fuzzy lop - LLVM-mode instrumentation pass
   ---------------------------------------------------

   Written by Laszlo Szekeres <lszekeres@google.com> and
              Michal Zalewski <lcamtuf@google.com>

   LLVM integration design comes from Laszlo Szekeres. C bits copied-and-pasted
   from afl-as.c are Michal's fault.

   This library is plugged into LLVM when invoking clang through afl-clang-fast.
   It tells the compiler to add code roughly equivalent to the bits discussed
   in ../afl-as.h.
*/

#define AFL_LLVM_PASS

#include "../config.h"
#include "../debug.h"

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <set>
#include <unordered_map>

#include <algorithm>

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/CFG.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;
using namespace std;

namespace {

  class AFLCoverage : public ModulePass {

    public:

      static char ID;
      AFLCoverage() : ModulePass(ID) { }

      bool runOnModule(Module &M) override;

      void calcSizes(int v);

      void distribute(int v, const set<int> &available);

      static const int MAX_N = 100000;

      vector<int> g[MAX_N];
      bool used[MAX_N];
      int sz[MAX_N];
      set<int> distribution[MAX_N];

  };

}


char AFLCoverage::ID = 0;

void AFLCoverage::calcSizes(int v){
  sz[v] = 1;
  used[v] = true;
  for (int to : g[v]) {
    if(used[to]) continue;
    calcSizes(to);
    sz[v] += sz[to];
  }
}

void AFLCoverage::distribute(int v, const set<int> &available){
  
  used[v] = true;

  if(available.size() == 0) return;

  vector<pair<int, int>> sizes;
  int sum = 0;
  for (int to : g[v]) {
    if(used[to])continue;
    sizes.push_back(make_pair(sz[to], to));
    sum += sz[to];
  }
  std::sort(sizes.begin(), sizes.end());
  int fuzzNumber = available.size();
  int eachFuzzer = (sum / fuzzNumber) + (sum % fuzzNumber != 0);

  int idSz = 0;
  int currentResp = 0;
  for (int i : available) {
    while (idSz < sizes.size() &&
           currentResp + sizes[idSz].first <= eachFuzzer) {
      currentResp += sizes[idSz].first;
      distribution[sizes[idSz].second].insert(i);
      idSz++;
    }
    if (idSz < sizes.size()) {
      int nodeId = sizes[idSz].second;
      currentResp -= eachFuzzer;
      if (currentResp == 0)
        continue;
      distribution[nodeId].insert(i);
    } else {
      idSz = 0;
    }
  }
  for (int to : g[v]) {
    if(used[to])continue;

    distribute(to, distribution[to]);
  }
}

bool AFLCoverage::runOnModule(Module &M) {


  const char* env_var_fuzz_num = "FUZZER_NUM";

  const char* env_var_fuzz_num_value = getenv(env_var_fuzz_num);
  int numberOfFuzzers = 1;
   numberOfFuzzers = atoi(env_var_fuzz_num_value);
  

  const char* env_var_fuzz_id = "FUZZER_ID";

  const char* env_var_fuzz_id_value = getenv(env_var_fuzz_id);
  int fuzzerId = 1;
   fuzzerId = atoi(env_var_fuzz_id_value);
  

  ACTF("Number of fuzzers is %d and fuzzer id is %d", numberOfFuzzers, fuzzerId);

  LLVMContext &C = M.getContext();

  IntegerType *Int8Ty  = IntegerType::getInt8Ty(C);
  IntegerType *Int32Ty = IntegerType::getInt32Ty(C);

  /* Show a banner */

  char be_quiet = 0;

  if (isatty(2) && !getenv("AFL_QUIET")) {

    SAYF(cCYA "afl-llvm-pass " cBRI VERSION cRST " by <lszekeres@google.com>\n");

  } else be_quiet = 1;

  /* Decide instrumentation ratio */

  char* inst_ratio_str = getenv("AFL_INST_RATIO");
  unsigned int inst_ratio = 100;

  if (inst_ratio_str) {

    if (sscanf(inst_ratio_str, "%u", &inst_ratio) != 1 || !inst_ratio ||
        inst_ratio > 100)
      FATAL("Bad value of AFL_INST_RATIO (must be between 1 and 100)");

  }

  /* Get globals for the SHM region and the previous location. Note that
     __afl_prev_loc is thread-local. */

  GlobalVariable *AFLMapPtr =
      new GlobalVariable(M, PointerType::get(Int8Ty, 0), false,
                         GlobalValue::ExternalLinkage, 0, "__afl_area_ptr");

  GlobalVariable *AFLPrevLoc = new GlobalVariable(
      M, Int32Ty, false, GlobalValue::ExternalLinkage, 0, "__afl_prev_loc",
      0, GlobalVariable::GeneralDynamicTLSModel, 0, false);

  /* Instrument all the things! */

  map<BasicBlock *, int> mp;
  
  bool isRoot[MAX_N];
  fill(isRoot, isRoot + MAX_N, true);
  int cnt = 0;
  for (auto &F : M){
    for (auto &BB : F) {
      
      BasicBlock * ptrBB = &BB;

      if(!mp.count(ptrBB)){
        mp[ptrBB] = cnt++;
      }

      for(BasicBlock *Pred : predecessors(&BB)){


        if(!mp.count(Pred)){
          mp[Pred] = cnt++;
        }

        int parentNode = mp[Pred];
        int childNode = mp[ptrBB];
        g[parentNode].push_back(childNode);
        isRoot[childNode] = false;
        //ACTF("Block id of the parent is %s for block %s \n", parentID.c_str(), bbId.c_str());
      }
    }
  }


  for (size_t i = 0; i < cnt; i++)
  {
    if(isRoot[i]){
      for (size_t j = 1; j <= numberOfFuzzers; j++)
      {
        distribution[i].insert(j);
      }
      calcSizes(i);
    }
  }
  fill(used, used + MAX_N, false);
  for (size_t i = 0; i < cnt; i++) {
    if (isRoot[i]) {
     // errs() << "Now block id: "<<  i << "\n";
      distribute(i, distribution[i]);
    }
  }


  int inst_blocks = 0;
  for (auto &F : M){
    for (auto &BB : F) {


      BasicBlock * ptrBB = &BB;
      //errs() << "Responsible fuzzers for block with ptr " << ptrBB << " are : ";

      //for(int id: distribution[mp[ptrBB]]){
       // errs() << id << " ";
      //}
      //errs() << "\n";
      if(!distribution[mp[ptrBB]].count(fuzzerId)) continue;
      BasicBlock::iterator IP = BB.getFirstInsertionPt();
      IRBuilder<> IRB(&(*IP));

      if (AFL_R(100) >= inst_ratio) continue;

      /* Make up cur_loc */

      unsigned int cur_loc = AFL_R(MAP_SIZE);

      ConstantInt *CurLoc = ConstantInt::get(Int32Ty, cur_loc);

      /* Load prev_loc */

      LoadInst *PrevLoc = IRB.CreateLoad(AFLPrevLoc);
      PrevLoc->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *PrevLocCasted = IRB.CreateZExt(PrevLoc, IRB.getInt32Ty());

      /* Load SHM pointer */

      LoadInst *MapPtr = IRB.CreateLoad(AFLMapPtr);
      MapPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *MapPtrIdx =
          IRB.CreateGEP(MapPtr, IRB.CreateXor(PrevLocCasted, CurLoc));

      /* Update bitmap */

      LoadInst *Counter = IRB.CreateLoad(MapPtrIdx);
      Counter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *Incr = IRB.CreateAdd(Counter, ConstantInt::get(Int8Ty, 1));
      IRB.CreateStore(Incr, MapPtrIdx)
          ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      /* Set prev_loc to cur_loc >> 1 */

      StoreInst *Store =
          IRB.CreateStore(ConstantInt::get(Int32Ty, cur_loc >> 1), AFLPrevLoc);
      Store->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      inst_blocks++;

    }
  }


  /* Say something nice. */

  if (!be_quiet) {

    if (!inst_blocks) WARNF("No instrumentation targets found.");
    else OKF("Instrumented %u locations (%s mode, ratio %u%%).",
             inst_blocks, getenv("AFL_HARDEN") ? "hardened" :
             ((getenv("AFL_USE_ASAN") || getenv("AFL_USE_MSAN")) ?
              "ASAN/MSAN" : "non-hardened"), inst_ratio);

  }

  return true;

}


static void registerAFLPass(const PassManagerBuilder &,
                            legacy::PassManagerBase &PM) {
  PM.add(new AFLCoverage());

}


static RegisterStandardPasses RegisterAFLPass(
    PassManagerBuilder::EP_ModuleOptimizerEarly, registerAFLPass);

static RegisterStandardPasses RegisterAFLPass0(
    PassManagerBuilder::EP_EnabledOnOptLevel0, registerAFLPass);
