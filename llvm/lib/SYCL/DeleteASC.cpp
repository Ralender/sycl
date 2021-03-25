//===- DeleteASC.cpp - remove address space cast              -------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception//
//===----------------------------------------------------------------------===//
//
// remove addressspace cast by propagating addressspace from sources to uses.
// many paterns of IR are not handled yet. but they usually not frequent. hard
// to handle.
// limitations include:
//  - cannot handle phi and selects during rewriting (fixable)
//  - cannot handle extrenal function that need rewriting (unfixable/impossible)
//  - cannot handle pointer hidden in structs or in memory (improvable).
//
//===----------------------------------------------------------------------===//

#include "llvm/SYCL/DeleteASC.h"
#include "llvm/ADT/MapVector.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/ConstantFolder.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Operator.h"
#include "llvm/Pass.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/ValueMapper.h"

using namespace llvm;

#define DEBUG_TYPE "del-asc"

namespace {

struct DeleteASC : public ModulePass {
  static char ID;
  bool Changed;
  int RecLvl = 0;
  std::unique_ptr<CallGraph> CG;

  using ChangeTy = std::pair<Use *, Value *>;
  SmallSetVector<Value *, 8> MaybeDelete;
  SmallVector<std::pair<Value *, Value *>, 8> ReWriteStack;

  enum : unsigned { ReturnIdx = ~(0u) };

  Type *editFunctionType(FunctionType *FTy,
                         ArrayRef<std::pair<unsigned, Type *>> Changes) {
    SmallVector<Type *, 8> TypeArgs;
    for (unsigned i = 0; i < FTy->getFunctionNumParams(); i++)
      for (auto &E : Changes)
        if (E.first == i)
          TypeArgs.push_back(E.second);
        else
          TypeArgs.push_back(FTy->getFunctionParamType(i));
    Type *ReturnTy = FTy->getReturnType();
    for (auto &E : Changes)
      if (E.first == ReturnIdx)
        ReturnTy = E.second;
    return FunctionType::get(ReturnTy, TypeArgs, FTy->isVarArg())
        ->getPointerTo(0);
  }

  Function *ChangeFunctionType(Function *F,
                               std::pair<unsigned, Type *> Change) {
    std::vector<Type *> ArgTypes;
    ValueToValueMapTy VMap;
    ClonedCodeInfo *CodeInfo = nullptr;

    for (const Argument &I : F->args())
      if (Change.first == I.getArgNo())
        ArgTypes.push_back(Change.second);
      else
        ArgTypes.push_back(I.getType());

    Type *ReturnTy = F->getFunctionType()->getReturnType();
    if (Change.first == ReturnIdx)
      ReturnTy = Change.second;
    FunctionType *FTy =
        FunctionType::get(ReturnTy, ArgTypes, F->getFunctionType()->isVarArg());
    Function *NewF =
        Function::Create(FTy, F->getLinkage(), F->getAddressSpace(),
                         F->getName(), F->getParent());

    Function::arg_iterator DestI = NewF->arg_begin();
    for (const Argument &I : F->args()) {
      DestI->setName(I.getName());
      VMap[&I] = &*DestI++;
    }

    SmallVector<ReturnInst *, 8> Returns; // Ignore returns cloned.
    CloneFunctionInto(NewF, F, VMap, F->getSubprogram() != nullptr, Returns, "",
                      CodeInfo);

    return NewF;
  }

  Value *modifyInst(Instruction *V, ChangeTy Change) {
    auto getInNewAddrSpace = [&](auto *Ty, auto *Ptr) {
      return Ty->getPointerElementType()->getPointerTo(
          Ptr->getType()->getPointerAddressSpace());
    };
    if (auto *BC = dyn_cast<BitCastInst>(V)) {
      V->mutateType(getInNewAddrSpace(V->getType(), Change.second));
      V->getOperandUse(0 /*Pointer operand*/).set(Change.second);
      return V;
    }
    if (auto *GEP = dyn_cast<GetElementPtrInst>(V)) {
      V->mutateType(getInNewAddrSpace(V->getType(), Change.second));
      V->getOperandUse(0 /*Pointer operand*/).set(Change.second);
      return V;
    }
    if (auto *L = dyn_cast<LoadInst>(V)) {
      V->getOperandUse(0 /*Pointer operand*/).set(Change.second);
      return nullptr;
    }
    if (auto *S = dyn_cast<StoreInst>(V)) {
      V->getOperandUse(1 /*Pointer operand*/).set(Change.second);
      return nullptr;
    }
    if (auto *ASC = dyn_cast<AddrSpaceCastInst>(V)) {
      MaybeDelete.insert(ASC);
      return Change.second;
    }
    if (auto *CB = dyn_cast<CallBase>(V)) {
      CB->getOperandUse(Change.first->getOperandNo()).set(Change.second);
      auto *F = CB->getCalledFunction();
      MaybeDelete.insert(F);
      auto *NewF = ChangeFunctionType(
          F, {Change.first->getOperandNo(), Change.second->getType()});
      CB->mutateType(NewF->getFunctionType()->getReturnType());
      CB->mutateFunctionType(NewF->getFunctionType());
      CB->setCalledFunction(NewF);

      ReWriteStack.emplace_back(NewF->getArg(Change.first->getOperandNo()),
                                NewF->getArg(Change.first->getOperandNo()));
      return nullptr;
    }
    if (auto *RI = dyn_cast<ReturnInst>(V)) {
      RI->getOperandUse(Change.first->getOperandNo()).set(Change.second);
      auto *NewF = ChangeFunctionType(V->getFunction(),
                                      {ReturnIdx, Change.second->getType()});
      MaybeDelete.insert(V->getFunction());

      for (Use &U : V->getFunction()->uses()) {
        if (auto *CB = dyn_cast<CallBase>(U.getUser())) {
          CB->mutateType(NewF->getFunctionType()->getReturnType());
          CB->mutateFunctionType(NewF->getFunctionType());
          CB->setCalledFunction(NewF);
          ReWriteStack.emplace_back(CB, CB);
        }
      }
      return nullptr;
    }
    V->getOperandUse(Change.first->getOperandNo()).set(Change.second);
    if (V->getType()->isPointerTy())
      return V;
    return nullptr;

    /// TODO implement missing rewrites
    /// phi, select...
    // V->dump();
    // llvm_unreachable("unimplemented modify");
  }

  void modifyUseChain(Value *V, Value *R) {
    SmallVector<ChangeTy, 8> Stack;
    for (Use &U : V->uses())
      Stack.emplace_back(&U, R);
    while (!Stack.empty()) {
      ChangeTy C = Stack.pop_back_val();
      auto *V = C.first->getUser();

      LLVM_DEBUG(llvm::dbgs() << "OLD:" << *V << '\n');
      auto *New = modifyInst(cast<Instruction>(V), C);
      LLVM_DEBUG(llvm::dbgs() << "NEW:" << *V << '\n');

      if (!New)
        continue;
      for (Use &U : V->uses())
        Stack.emplace_back(&U, New);
    }
  }

  void handleFunction(Function *F) {
    SmallVector<WeakVH, 8> ASCs;

    for (auto &I : instructions(F))
      if (auto *ASC = dyn_cast<AddrSpaceCastInst>(&I))
        ASCs.push_back(ASC);

    for (auto &E : ASCs) {
      if (!E)
        continue;
      Changed = true;
      auto *ASC = cast<AddrSpaceCastInst>(E);
#ifndef NDEBUG
      SmallVector<const Value *, 4> Sources;
      /// This is needed for correctness not just optimization so not limits.
      getUnderlyingObjects(ASC, Sources, nullptr,
                           std::numeric_limits<unsigned>::max());
      unsigned SrcASC = Sources[0]->getType()->getPointerAddressSpace();
      for (auto *Ptr : Sources) {
        assert(Ptr->getType()->getPointerAddressSpace() == SrcASC &&
               "the address space of is not staticly computable.");
      }
#endif

      MaybeDelete.insert(ASC);
      ReWriteStack.emplace_back(ASC, ASC->getPointerOperand());
    }
  }

  DeleteASC() : ModulePass(ID) {}
  bool runOnModule(Module &M) override {
    for (auto &F : M)
      handleFunction(&F);

    while (!ReWriteStack.empty()) {
      auto C = ReWriteStack.pop_back_val();
      modifyUseChain(C.first, C.second);
    }

    for (Value *V : MaybeDelete) {
      if (auto *F = dyn_cast<Function>(V)) {
        if (V->use_empty())
          F->eraseFromParent();
        continue;
      }
      if (auto *I = dyn_cast<Instruction>(V)) {
        if (I->use_empty())
          RecursivelyDeleteTriviallyDeadInstructions(I);
        continue;
      }
      llvm_unreachable("unimplemented");
    }
    return Changed;
  }

  virtual llvm::StringRef getPassName() const override { return "DeleteASC"; }
};
} // namespace

namespace llvm {
void initializeDeleteASCPass(PassRegistry &Registry);
}

INITIALIZE_PASS(DeleteASC, "del-asc", "delete address spaces", false, false)
ModulePass *llvm::createDeleteASCPass() { return new DeleteASC(); }

char DeleteASC::ID = 0;
