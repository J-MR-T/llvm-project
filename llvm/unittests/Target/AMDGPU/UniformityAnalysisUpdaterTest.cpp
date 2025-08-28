
#include "llvm/Analysis/UniformityAnalysisUpdater.h"
#include "AMDGPUTargetMachine.h"
#include "AMDGPUUnitTests.h"
#include "llvm-c/Core.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/Analysis/UniformityAnalysis.h"
#include "llvm/AsmParser/Parser.h"
#include "llvm/BinaryFormat/Dwarf.h"
#include "llvm/BinaryFormat/MsgPack.h"
#include "llvm/CodeGen/RDFGraph.h"
#include "llvm/FuzzMutate/FuzzerCLI.h"
#include "llvm/FuzzMutate/RandomIRBuilder.h"
#include "llvm/IR/CycleInfo.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"

#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/Local.h"
#include "gtest/gtest.h"

// Inspired by DomTreeUpdaterTest.cpp

using namespace llvm;

#define DEBUG_TYPE "uniformity-analysis-updater-test"

// TODO Less code duplication between these tests, by creating an actual test
// class to unify some of the before/after test functionality.

// TODO Also should reduce duplication between these tests and the regression
// tests, some of these are copied and/or adjusted from there.

auto initiallyComputeUniformityAnalysis(TargetTransformInfo *TTI, Function *F) {
  auto DT = std::make_unique<DominatorTree>(*F);
  auto CI = std::make_unique<CycleInfo>();
  CI->compute(*F);

  UniformityInfo Unif(*DT, *CI, TTI);
  Unif.compute();

  return std::make_tuple(std::move(DT), std::move(CI), std::move(Unif));
}

template <typename T> constexpr auto divergenceStr(T &Info, Instruction *Inst) {
  return (Info.isDivergent(Inst) ? "divergent" : "uniform");
}

template <typename T, typename R>
bool analysesMatch(T &ToTest, R &Oracle, Function *F) {
  for (auto &Inst : instructions(F))
    if (ToTest.isDivergent(&Inst) != Oracle.isDivergent(&Inst)) {
      dbgs() << "Value " << Inst << " doesn't match, updated analysis says: "
             << divergenceStr(ToTest, &Inst)
             << "; fresh analysis says: " << divergenceStr(Oracle, &Inst)
             << "\n";
      return false;
    }

  for (auto &Arg : F->args())
    if (ToTest.isDivergent(&Arg) != Oracle.isDivergent(&Arg))
      return false;

  return true;
}

bool matchesAFreshAnalysis(UniformityAnalysisUpdater &Updater,
                           TargetTransformInfo *TTI, Function *F) {
  LLVM_DEBUG(dbgs() << "FRESH ANALYSIS COMPUTE: START\n");
  auto [_1, _2, UnifFresh] = initiallyComputeUniformityAnalysis(TTI, F);
  LLVM_DEBUG(dbgs() << "FRESH ANALYSIS COMPUTE: DONE\n");

  return analysesMatch(Updater, UnifFresh, F);
}

#define EXPECT_UNIFORM(Inst) EXPECT_FALSE(Updater.isDivergent((Inst)));

#define EXPECT_DIVERGENT(Inst) EXPECT_TRUE(Updater.isDivergent((Inst)));

#define EXPECT_MATCHES_FRESH_ANALYSIS()                                        \
  EXPECT_TRUE(matchesAFreshAnalysis(Updater, &TTI, F))

#define ASSERT_NAME(X, expectedName)                                           \
  ASSERT_STREQ((X).getName().str().c_str(), (expectedName));

TEST(UniformityAnalysisUpdater, SyntheticInsert1) {
  StringRef FuncName = "f";
  StringRef ModuleString = R"(
                          define amdgpu_kernel i32 @f(i32 %i) {
                          bb0:
                            %tid.x = call i32 @llvm.amdgcn.workitem.id.x()
                            %stackAllocaSp1 = alloca i32, addrspace(1)
                            %stackAllocaSp5 = alloca i32, addrspace(5)
                            %uniform = load i32, ptr addrspace(1) %stackAllocaSp1
                            %sourceOfDivergence1 = load i32, ptr addrspace(5) %stackAllocaSp5
                            ret i32 3
                          }
                          )";
  //%tid.x = call i32 @llvm.amdgcn.workitem.id.x()
  //%stackAlloca = alloca i64, addrspace(5)
  //%sourceOfDivergence1 = load i64, ptr addrspace(5) %stackAlloca
  // Make the module.
  LLVMContext Context;
  SMDiagnostic Err;
  std::unique_ptr<Module> M = parseAssemblyString(ModuleString, Err, Context);
  ASSERT_TRUE(M) << "Bad LLVM IR as test input?";
  Function *F = M->getFunction(FuncName);

  auto TM =
      createAMDGPUTargetMachine("amdgcn-amd-", "gfx1010", "+wavefrontsize32");
  auto TTI = TM->getTargetTransformInfo(*F);

  Function::iterator FI = F->begin();
  BasicBlock *BB0 = &*FI++;
  // BasicBlock *BB1 = &*FI++;
  // BasicBlock *BB2 = &*FI++;
  // BasicBlock *BB3 = &*FI++;

  auto &AddrSp1Load = *BB0->getTerminator()->getPrevNode()->getPrevNode();
  auto &AddrSp5Load = *BB0->getTerminator()->getPrevNode();
  auto &ThreadId = *BB0->getFirstNonPHIIt();

  auto [DT, CI, Unif] = initiallyComputeUniformityAnalysis(&TTI, F);

  // sanity check with an ASSERT, not because we couldnt continue, but if this
  // is already wrong, the rest of the test will be utterly wrong
  ASSERT_TRUE(Unif.isDivergent(&AddrSp5Load));

  UniformityAnalysisUpdater Updater(Unif);

  IRBuilder<> IRB(BB0);
  IRB.SetInsertPoint(BB0->getTerminator());

  auto *DivergentAdd1 =
      dyn_cast<Instruction>(IRB.CreateAdd(&AddrSp5Load, &ThreadId));
  EXPECT_DIVERGENT(DivergentAdd1);

  auto *DivergentAdd2 =
      dyn_cast<Instruction>(IRB.CreateAdd(&AddrSp5Load, IRB.getInt32(42)));
  EXPECT_DIVERGENT(DivergentAdd2);

  auto *DivergentAdd3 =
      dyn_cast<Instruction>(IRB.CreateAdd(IRB.getInt32(42), &ThreadId));
  EXPECT_DIVERGENT(DivergentAdd3);

  auto *UniformAdd =
      dyn_cast<Instruction>(IRB.CreateAdd(IRB.getInt32(42), &AddrSp1Load));
  EXPECT_UNIFORM(UniformAdd);

  auto *StrungTogetherDivergentAdd = dyn_cast<Instruction>(IRB.CreateAdd(
      IRB.getInt32(42),
      IRB.CreateAdd(IRB.CreateAdd(
                        // this divergence needs to propagate
                        IRB.CreateAdd(&AddrSp5Load, IRB.getInt32(42), "A"),
                        IRB.CreateAdd(&AddrSp1Load, &AddrSp1Load, "B"), "C"),
                    IRB.CreateAdd(IRB.getInt32(42), &AddrSp1Load, "D"), "E"),
      "F"));
  EXPECT_DIVERGENT(StrungTogetherDivergentAdd);

  EXPECT_MATCHES_FRESH_ANALYSIS();

  // delete them again
  for (auto &Inst : {StrungTogetherDivergentAdd, DivergentAdd1, DivergentAdd2,
                     DivergentAdd3, UniformAdd}) {
    RecursivelyDeleteTriviallyDeadInstructions(Inst);
    Updater.informAboutDeletion(Inst);
  }

  EXPECT_MATCHES_FRESH_ANALYSIS();
}

TEST(UniformityAnalysisUpdater, SyntheticReplace1) {
  StringRef FuncName = "f";
  StringRef ModuleString = R"(
                          define amdgpu_kernel i32 @f(i32 %i) {
                          bb0:
                            %tid.x = call i32 @llvm.amdgcn.workitem.id.x()
                            %stackAllocaSp1 = alloca i32, addrspace(1)
                            %stackAllocaSp5 = alloca i32, addrspace(5)
                            %uniform = load i32, ptr addrspace(1) %stackAllocaSp1
                            %sourceOfDivergence1 = load i32, ptr addrspace(5) %stackAllocaSp5
                            br label %bb1
                          bb1:
                            %transitivelyUniform = add i32 %uniform, %uniform
                            %transitivelyUniform2 = add i32 %transitivelyUniform, %uniform
                            %transitivelyDivergent = sub i32 %transitivelyUniform2, %sourceOfDivergence1
                            ; importantly: need to stop the iteration before it reaches here
                            ret i32 %sourceOfDivergence1
                          }
                          )";
  //%tid.x = call i32 @llvm.amdgcn.workitem.id.x()
  //%stackAlloca = alloca i64, addrspace(5)
  //%sourceOfDivergence1 = load i64, ptr addrspace(5) %stackAlloca
  // Make the module.
  LLVMContext Context;
  SMDiagnostic Err;
  std::unique_ptr<Module> M = parseAssemblyString(ModuleString, Err, Context);
  ASSERT_TRUE(M) << "Bad LLVM IR as test input? Error: " << Err.getMessage()
                 << "\n---\nLine/Col: " << Err.getLineNo() << "/"
                 << Err.getColumnNo();

  Function *F = M->getFunction(FuncName);

  auto TM =
      createAMDGPUTargetMachine("amdgcn-amd-", "gfx1010", "+wavefrontsize32");
  auto TTI = TM->getTargetTransformInfo(*F);

  Function::iterator FI = F->begin();
  BasicBlock *BB0 = &*FI++;
  BasicBlock *BB1 = &*FI++;

  auto &TransitivelyUniform =
      *BB1->getTerminator()->getPrevNode()->getPrevNode()->getPrevNode();
  auto &AddrSp5Load = *BB0->getTerminator()->getPrevNode();
  auto &ThreadId = *BB0->getFirstNonPHIIt();

  auto [DT, CI, Unif] = initiallyComputeUniformityAnalysis(&TTI, F);

  // sanity check with an ASSERT, not because we couldnt continue, but if this
  // is already wrong, the rest of the test will be utterly wrong
  ASSERT_TRUE(Unif.isDivergent(&AddrSp5Load));

  UniformityAnalysisUpdater Updater(Unif);

  IRBuilder<> IRB(BB0);
  IRB.SetInsertPoint(BB0->getTerminator());

  auto *DivergentAdd1 =
      dyn_cast<Instruction>(IRB.CreateAdd(&AddrSp5Load, &ThreadId));
  auto *DivergentAdd2 =
      dyn_cast<Instruction>(IRB.CreateAdd(DivergentAdd1, IRB.getInt32(42)));
  auto *DivergentAdd3 =
      dyn_cast<Instruction>(IRB.CreateAdd(IRB.getInt32(42), DivergentAdd2));
  EXPECT_DIVERGENT(DivergentAdd3);

  // testing case 3 from `informAboutRAUW`
  TransitivelyUniform.replaceAllUsesWith(DivergentAdd3);
  Updater.informAboutRAUW(&TransitivelyUniform, DivergentAdd3);

  // case 3 should be handled exactly the same as a fresh analysis
  EXPECT_MATCHES_FRESH_ANALYSIS();
}

TEST(UniformityAnalysisUpdater, SyntheticReplace2WithTerminator) {
  StringRef FuncName = "f";
  StringRef ModuleString = R"(
                          define amdgpu_kernel i32 @f(i32 %i) {
                          bb0:
                            %tid.x = call i32 @llvm.amdgcn.workitem.id.x()
                            %stackAllocaSp1 = alloca i32, addrspace(1)
                            %stackAllocaSp5 = alloca i32, addrspace(5)
                            %uniform = load i32, ptr addrspace(1) %stackAllocaSp1
                            %sourceOfDivergence1 = load i32, ptr addrspace(5) %stackAllocaSp5
                            br label %bb1
                          bb1:
                            %transitivelyUniform = add i32 %uniform, %uniform
                            %transitivelyUniform2 = add i32 %transitivelyUniform, %uniform
                            %transitivelyDivergent = sub i32 %transitivelyUniform2, %sourceOfDivergence1
                            ; importantly: we're also replacing the terminator!
                            ret i32 %transitivelyUniform2
                          }
                          )";
  //%tid.x = call i32 @llvm.amdgcn.workitem.id.x()
  //%stackAlloca = alloca i64, addrspace(5)
  //%sourceOfDivergence1 = load i64, ptr addrspace(5) %stackAlloca
  // Make the module.
  LLVMContext Context;
  SMDiagnostic Err;
  std::unique_ptr<Module> M = parseAssemblyString(ModuleString, Err, Context);
  ASSERT_TRUE(M) << "Bad LLVM IR as test input? Error: " << Err.getMessage()
                 << "\n---\nLine/Col: " << Err.getLineNo() << "/"
                 << Err.getColumnNo();

  Function *F = M->getFunction(FuncName);

  auto TM =
      createAMDGPUTargetMachine("amdgcn-amd-", "gfx1010", "+wavefrontsize32");
  auto TTI = TM->getTargetTransformInfo(*F);

  Function::iterator FI = F->begin();
  BasicBlock *BB0 = &*FI++;
  BasicBlock *BB1 = &*FI++;

  auto &TransitivelyUniform =
      *BB1->getTerminator()->getPrevNode()->getPrevNode()->getPrevNode();
  auto &AddrSp5Load = *BB0->getTerminator()->getPrevNode();
  auto &ThreadId = *BB0->getFirstNonPHIIt();

  auto [_1, _2, Unif] = initiallyComputeUniformityAnalysis(&TTI, F);

  // sanity check with an ASSERT, not because we couldnt continue, but if this
  // is already wrong, the rest of the test will be utterly wrong
  ASSERT_TRUE(Unif.isDivergent(&AddrSp5Load));

  UniformityAnalysisUpdater Updater(Unif);

  IRBuilder<> IRB(BB0);
  IRB.SetInsertPoint(BB0->getTerminator());

  auto *DivergentAdd1 =
      dyn_cast<Instruction>(IRB.CreateAdd(&AddrSp5Load, &ThreadId));
  auto *DivergentAdd2 =
      dyn_cast<Instruction>(IRB.CreateAdd(DivergentAdd1, IRB.getInt32(42)));
  auto *DivergentAdd3 =
      dyn_cast<Instruction>(IRB.CreateAdd(IRB.getInt32(42), DivergentAdd2));
  EXPECT_DIVERGENT(DivergentAdd3);

  // testing case 3 from `informAboutRAUW`
  TransitivelyUniform.replaceAllUsesWith(DivergentAdd3);
  Updater.informAboutRAUW(&TransitivelyUniform, DivergentAdd3);

  // case 3 should be handled exactly the same as a fresh analysis
  EXPECT_MATCHES_FRESH_ANALYSIS();
}

// TODO this is from hiddne_loopdiverge.ll, see if we can avoid the code dupe
TEST(UniformityAnalysisUpdater,
     SyntheticReplaceAllUniformWithLotsOfDivergence) {
  StringRef FuncName = "hidden_loop_diverge";

  // NOTE: in the test function, the CHECK checks indicate what should happen
  // when the %tid is actually divergent,
  //       as would be the case if the original definition wasn't commented out.
  StringRef ModuleString = R"(
define amdgpu_kernel void @hidden_loop_diverge(i32 %n, i32 %a, i32 %b) #0 {
; CHECK-NOT: DIVERGENT: %uni.
; CHECK-NOT: DIVERGENT: br i1 %uni.

entry:
  %tidOriginalAndUnused = call i32 @llvm.amdgcn.workitem.id.x()
  ; replace tid's definition with anything that's uniform -> initial analysis should mean all of it is uniform
  %tid = add i32 %a, %b
  %uni.cond = icmp slt i32 %a, 0
  br i1 %uni.cond, label %X, label %H  ; uniform

H:
  %uni.merge.h = phi i32 [ 0, %entry ], [ %uni.inc, %B ]
  %div.exitx = icmp slt i32 %tid, 0
  br i1 %div.exitx, label %X, label %B ; divergent branch
; CHECK: DIVERGENT: %div.exitx =
; CHECK: DIVERGENT: br i1 %div.exitx,

B:
  %uni.inc = add i32 %uni.merge.h, 1
  %div.exity = icmp sgt i32 %tid, 0
  br i1 %div.exity, label %Y, label %H ; divergent branch
; CHECK: DIVERGENT: %div.exity =
; CHECK: DIVERGENT: br i1 %div.exity,

X:
  %div.merge.x = phi i32 [ %a, %entry ], [ %uni.merge.h, %H ] ; temporal divergent phi
  br i1 %uni.cond, label %Y, label %exit
; CHECK: DIVERGENT: %div.merge.x =

Y:
  %div.merge.y = phi i32 [ 42, %X ], [ %b, %B ]
  br label %exit
; CHECK: DIVERGENT: %div.merge.y =

exit:
  %div.merge.exit = phi i32 [ %a, %X ], [ %b, %Y ]
  ret void
; CHECK: DIVERGENT: %div.merge.exit =
}
                          )";
  // Make the module.
  LLVMContext Context;
  SMDiagnostic Err;
  std::unique_ptr<Module> M = parseAssemblyString(ModuleString, Err, Context);
  ASSERT_TRUE(M) << "Bad LLVM IR as test input? Error: " << Err.getMessage()
                 << "\n---\nLine/Col: " << Err.getLineNo() << "/"
                 << Err.getColumnNo();

  Function *F = M->getFunction(FuncName);

  auto TM =
      createAMDGPUTargetMachine("amdgcn-amd-", "gfx1010", "+wavefrontsize32");
  auto TTI = TM->getTargetTransformInfo(*F);

  auto VMap = ValueToValueMapTy();
  Function *FWithoutTidOriginal = CloneFunction(F, VMap);

  // actually erase tidOriginalAndUnused
  FWithoutTidOriginal->begin()->begin()->eraseFromParent();

  auto [_1, _2, UnifWithoutTidOriginal] =
      initiallyComputeUniformityAnalysis(&TTI, FWithoutTidOriginal);

  // assert that the initial function has the expected uniformity, otherwise the
  // test is broken and the results will only be confusing
  for (auto &Inst : instructions(FWithoutTidOriginal))
    ASSERT_TRUE(UnifWithoutTidOriginal.isUniform(&Inst))
        << "Tested function is wrong somehow - should be entirely uniform";

  // === actual test start ===
  Function::iterator FI = F->begin();
  BasicBlock *BB0 = &*FI++;

  auto [_3, _4, Unif] = initiallyComputeUniformityAnalysis(&TTI, F);
  auto &tidOriginalAndUnused = *BB0->begin();
  auto &tidUniform = *BB0->begin()->getNextNode();
  auto Updater = UniformityAnalysisUpdater(Unif);

  // we want to make sure the updater properly propagates a change in divergence
  // from the start of the function to the very end
  tidUniform.replaceAllUsesWith(&tidOriginalAndUnused);
  Updater.informAboutRAUW(&tidUniform, &tidOriginalAndUnused);

  EXPECT_MATCHES_FRESH_ANALYSIS();
}

TEST(UniformityAnalysisUpdater, SyntheticInsertTemporallyDivergentUse) {

  StringRef FuncName = "temporal_diverge";
  StringRef ModuleString = R"(
define amdgpu_kernel void @temporal_diverge(i32 %n, i32 %a, i32 %b) #0 {
; CHECK-LABEL: for function 'temporal_diverge':
; CHECK-NOT: DIVERGENT: %uni.
; CHECK-NOT: DIVERGENT: br i1 %uni.

entry:
  %tid = call i32 @llvm.amdgcn.workitem.id.x()
  %uni.cond = icmp slt i32 %a, 0
  br label %H

H:
; CHECK-NOT: DIVERGENT: %uni.merge.h
  %uni.merge.h = phi i32 [ 0, %entry ], [ %uni.inc, %H ]
; CHECK-NOT: DIVERGENT: %uni.inc
  %uni.inc = add i32 %uni.merge.h, 1
; CHECK: DIVERGENT: %div.exitx =
  %div.exitx = icmp slt i32 %tid, 0
; CHECK: DIVERGENT: br i1 %div.exitx,
  br i1 %div.exitx, label %X, label %H ; divergent branch

X:
; CHECK: DIVERGENT:  %div.user =
  %div.user = add i32 %uni.inc, 5
  ret void
}
)";

  LLVMContext Context;
  SMDiagnostic Err;
  std::unique_ptr<Module> M = parseAssemblyString(ModuleString, Err, Context);
  ASSERT_TRUE(M) << "Bad LLVM IR as test input? Error: " << Err.getMessage()
                 << "\n---\nLine/Col: " << Err.getLineNo() << "/"
                 << Err.getColumnNo();

  Function *F = M->getFunction(FuncName);

  auto TM =
      createAMDGPUTargetMachine("amdgcn-amd-", "gfx1010", "+wavefrontsize32");
  auto TTI = TM->getTargetTransformInfo(*F);

  auto &BB_X = *--F->end();
  ASSERT_NAME(BB_X, "X");

  auto [_1, _2, Unif] = initiallyComputeUniformityAnalysis(&TTI, F);

  BinaryOperator *divUser = dyn_cast<BinaryOperator>(&*BB_X.begin());
  ASSERT_TRUE(Unif.isDivergent(divUser));

  IRBuilder<> IRB(&BB_X);
  auto *divUserAgain = IRB.CreateAdd(divUser->getOperand(0), IRB.getInt32(5));

  UniformityAnalysisUpdater Updater(Unif);
  EXPECT_DIVERGENT(divUserAgain);

  EXPECT_MATCHES_FRESH_ANALYSIS();

  // now try the same, but inserting a new cycle (that is in itself uniform),
  // and a termporally divergent use outside
  auto *uniInc = dyn_cast<Instruction>(divUser->getOperand(0));
  auto *uniMergeH = dyn_cast<Instruction>(uniInc->getOperand(0));

  IRB.SetInsertPoint(uniMergeH);
  auto *uniMergeHAgain = dyn_cast<PHINode>(uniMergeH->clone());
  auto *uniIncAgain = uniInc->clone();
  uniMergeHAgain->setIncomingValue(1, uniIncAgain);
  uniIncAgain->setOperand(0, uniMergeHAgain);

  IRB.Insert(uniMergeHAgain);
  IRB.SetInsertPoint(uniInc);
  IRB.Insert(uniIncAgain);

  // important: don't EXPECT_UNIFORM here! otherwise the traversal later on will
  // behave differently!

  IRB.SetInsertPoint(divUser);
  auto *temporallyDivergentUseOfNewValue =
      IRB.CreateAdd(uniIncAgain, IRB.getInt32(5));
  EXPECT_DIVERGENT(temporallyDivergentUseOfNewValue);
  EXPECT_UNIFORM(uniIncAgain);
  EXPECT_UNIFORM(uniMergeHAgain);

  EXPECT_MATCHES_FRESH_ANALYSIS();
}

TEST(UniformityAnalysisUpdater, SyntheticInsertDivergentPhiJoinNonCyclic) {

  StringRef FuncName = "divergent_phi_join";
  StringRef ModuleString = R"(
define amdgpu_kernel i32 @divergent_phi_join(i32 %n, i32 %a, i32 %b) #0 {
entry:
  %tid = call i32 @llvm.amdgcn.workitem.id.x()
  %div.cond = icmp slt i32 %tid, 0
  br i1 %div.cond, label %X, label %Y ; divergent branch
X:
  br label %Join
Y:
  br label %Join
Join:
  %div.phi = phi i32 [ 0, %X ], [ 1, %Y ]
  ret i32 %div.phi
}
)";

  LLVMContext Context;
  SMDiagnostic Err;
  std::unique_ptr<Module> M = parseAssemblyString(ModuleString, Err, Context);
  ASSERT_TRUE(M) << "Bad LLVM IR as test input? Error: " << Err.getMessage()
                 << "\n---\nLine/Col: " << Err.getLineNo() << "/"
                 << Err.getColumnNo();

  Function *F = M->getFunction(FuncName);

  auto TM =
      createAMDGPUTargetMachine("amdgcn-amd-", "gfx1010", "+wavefrontsize32");
  auto TTI = TM->getTargetTransformInfo(*F);

  auto &BB_Join = *--F->end();
  ASSERT_NAME(BB_Join, "Join");
  auto &BB_X = *F->begin()->getNextNode();
  auto &BB_Y = *F->begin()->getNextNode()->getNextNode();

  auto [_1, _2, Unif] = initiallyComputeUniformityAnalysis(&TTI, F);

  auto *divPhi = &*BB_Join.phis().begin();
  ASSERT_TRUE(Unif.isDivergent(divPhi));

  IRBuilder<> IRB(divPhi);
  // TODO maybe just clone instead?
  auto *divPhiAgain = IRB.CreatePHI(divPhi->getType(), 2);
  divPhiAgain->addIncoming(IRB.getInt32(0), &BB_X);
  divPhiAgain->addIncoming(IRB.getInt32(1), &BB_Y);

  UniformityAnalysisUpdater Updater(Unif);
  EXPECT_DIVERGENT(divPhiAgain);

  EXPECT_MATCHES_FRESH_ANALYSIS();
}

TEST(UniformityAnalysisUpdater, SyntheticDeleteAliasingProblems) {

  StringRef FuncName = "asm_mixed_sgpr_vgpr";
  StringRef ModuleString = R"(
define void @asm_mixed_sgpr_vgpr(i32 %divergent) {
  %asm = call { i32, i32 } asm "; def $0, $1, $2","=s,=v,v"(i32 %divergent)
  %sgpr = extractvalue { i32, i32 } %asm, 0
  %vgpr = extractvalue { i32, i32 } %asm, 1
  ret void
}
)";
  ASSERT_TRUE(ModuleString.contains(FuncName))
      << "Forgot to update function name?";

  LLVMContext Context;

  SMDiagnostic Err;
  std::unique_ptr<Module> M = parseAssemblyString(ModuleString, Err, Context);
  ASSERT_TRUE(M) << "Bad LLVM IR as test input? Error: " << Err.getMessage()
                 << "\n---\nLine/Col: " << Err.getLineNo() << "/"
                 << Err.getColumnNo();

  Function *F = M->getFunction(FuncName);

  auto TM =
      createAMDGPUTargetMachine("amdgcn-amd-", "gfx1010", "+wavefrontsize32");
  auto TTI = TM->getTargetTransformInfo(*F);

  auto [_1, _2, Unif] = initiallyComputeUniformityAnalysis(&TTI, F);

  auto *sgpr = dyn_cast<ExtractValueInst>(F->begin()->begin()->getNextNode());

  UniformityAnalysisUpdater Updater(Unif);

  ASSERT_TRUE(TTI.isAlwaysUniform(sgpr));

  // don't need to replace, because sgpr has no uses anyway
  // DONT actually delete (`eraseFromParent()`) it! we basically want to
  // simulate what happens when a new instruction gets allocated to this spot
  sgpr->removeFromParent();
  Updater.informAboutDeletion(sgpr);

  // -> simulate this, by just editing the sgpr so that its basically the same
  // instruction as the vgpr. The vgpr should definitely be divergent, but if
  // sgpr was not removed from both KnownValues and UniformOverrides, it will be
  // marked uniform by the updater
  // TODO Think about whether to leave it like this. This *should* technically
  // be safe, because the underlying thing is just a vector that doesn't hold
  // const values, and only the way the pointer is returned means its const, but
  // it's still not nice.
  *const_cast<unsigned *>(sgpr->indices().begin()) = 1;

  // essentially treat sgpr as a newly inserted instruction (also need to
  // actually insert it again)
  IRBuilder<> IRB(F->begin()->getTerminator());
  IRB.Insert(sgpr);

  EXPECT_DIVERGENT(sgpr);
  EXPECT_MATCHES_FRESH_ANALYSIS();
}

TEST(UniformityAnalysisUpdater, SyntheticInsertDivergenceFromArgument) {
  StringRef FuncName = "f";
  StringRef ModuleString = R"(
define void @f(i32 %divergentArg) {
entry:
  ret void
}
)";
  ASSERT_TRUE(ModuleString.contains(FuncName))
      << "Forgot to update function name?";

  LLVMContext Context;

  SMDiagnostic Err;
  std::unique_ptr<Module> M = parseAssemblyString(ModuleString, Err, Context);
  ASSERT_TRUE(M) << "Bad LLVM IR as test input? Error: " << Err.getMessage()
                 << "\n---\nLine/Col: " << Err.getLineNo() << "/"
                 << Err.getColumnNo();

  Function *F = M->getFunction(FuncName);

  auto TM =
      createAMDGPUTargetMachine("amdgcn-amd-", "gfx1010", "+wavefrontsize32");
  auto TTI = TM->getTargetTransformInfo(*F);

  auto [_1, _2, Unif] = initiallyComputeUniformityAnalysis(&TTI, F);

  UniformityAnalysisUpdater Updater(Unif);

  IRBuilder IRB(&*F->begin()->begin());

  auto *add = IRB.CreateAdd(F->getArg(0), F->getArg(0));
  EXPECT_DIVERGENT(add);
}

TEST(UniformityAnalysisUpdater, SyntheticAutomaticCallbacks) {
  StringRef FuncName = "f";
  StringRef ModuleString = R"(
define amdgpu_kernel i32 @f(i32 %n, i32 %a, i32 %b) #0 {
entry:
  %tid = call i32 @llvm.amdgcn.workitem.id.x()
  %add = add i32 %a, %b
  %add2 = add i32 %add, %b
  ret i32 %add2
}
)";

  LLVMContext Context;
  SMDiagnostic Err;
  std::unique_ptr<Module> M = parseAssemblyString(ModuleString, Err, Context);
  ASSERT_TRUE(M) << "Bad LLVM IR as test input? Error: " << Err.getMessage()
                 << "\n---\nLine/Col: " << Err.getLineNo() << "/"
                 << Err.getColumnNo();

  Function *F = M->getFunction(FuncName);

  auto TM =
      createAMDGPUTargetMachine("amdgcn-amd-", "gfx1010", "+wavefrontsize32");
  auto TTI = TM->getTargetTransformInfo(*F);

  auto [_1, _2, Unif] = initiallyComputeUniformityAnalysis(&TTI, F);

  auto *tid = &*F->begin()->begin();
  auto *add = tid->getNextNode();
  auto *add2 = add->getNextNode();
  ASSERT_NAME(*add2, "add2");

  ASSERT_TRUE(Unif.isDivergent(tid));
  ASSERT_TRUE(Unif.isUniform(add));
  ASSERT_TRUE(Unif.isUniform(add2));

  auto *pImpl = F->getContext().pImpl;

  unsigned numRAUWBeforeUpdater = pImpl->AfterRAUWCallbacks.size();
  unsigned numDeleteBeforeUpdater = pImpl->AfterRAUWCallbacks.size();

  {
    UniformityAnalysisUpdater Updater(Unif, &Context);

    EXPECT_GE(pImpl->AfterRAUWCallbacks.size(), 1u);
    EXPECT_GE(pImpl->BeforeDeleteCallbacks.size(), 1u);

    add->replaceAllUsesWith(tid);

    EXPECT_DIVERGENT(add2);
    EXPECT_MATCHES_FRESH_ANALYSIS();
  }
  // test correct resource deallocation
  EXPECT_EQ(pImpl->AfterRAUWCallbacks.size(), numRAUWBeforeUpdater);
  EXPECT_EQ(pImpl->BeforeDeleteCallbacks.size(), numDeleteBeforeUpdater);
}

TEST(UniformityAnalysisUpdater, SyntheticAssumedDivergentCycles) {
  StringRef FuncName = "f";
  StringRef ModuleString = R"(
define amdgpu_kernel void @f(i32 %uni) {
entry:
  %tid = call i32 @llvm.amdgcn.workitem.id.x()
  %div.cond = icmp sgt i32 %tid, 0
; to get an AssumedDivergent cycle: need a join block that's inside a cycle
; -> then all values inside that cycle are assumed divergent
  br i1 %div.cond, label %x, label %y
x:
  br label %loopjoin
y:
  br label %loopjoin
loopjoin:
  %assumedDivergent = add i32 %uni, %uni
  br i1 %div.cond, label %x, label %y
}
)";
  ASSERT_TRUE(ModuleString.contains((" @" + FuncName).str()))
      << "Forgot to update function name?";

  LLVMContext Context;

  SMDiagnostic Err;
  std::unique_ptr<Module> M = parseAssemblyString(ModuleString, Err, Context);
  ASSERT_TRUE(M) << "Bad LLVM IR as test input? Error: " << Err.getMessage()
                 << "\n---\nLine/Col: " << Err.getLineNo() << "/"
                 << Err.getColumnNo();

  Function *F = M->getFunction(FuncName);

  auto TM =
      createAMDGPUTargetMachine("amdgcn-amd-", "gfx1010", "+wavefrontsize32");
  auto TTI = TM->getTargetTransformInfo(*F);

  auto [_1, _2, Unif] = initiallyComputeUniformityAnalysis(&TTI, F);

  auto *BB_Entry = &*F->begin();
  auto *BB_LoopJoin = BB_Entry->getNextNode()->getNextNode()->getNextNode();

  auto *assumedDivergent = &*BB_LoopJoin->begin();
  ASSERT_NAME(*assumedDivergent, "assumedDivergent");

  ASSERT_TRUE(Unif.isDivergent(assumedDivergent));

  UniformityAnalysisUpdater Updater(Unif, &Context);
  IRBuilder<> IRB(&*BB_LoopJoin->begin());

  EXPECT_DIVERGENT(IRB.CreateAdd(F->getArg(0), F->getArg(0)));
  EXPECT_MATCHES_FRESH_ANALYSIS();
}

TEST(UniformityAnalysisUpdater, SyntheticSDACacheInvalidation) {
  StringRef FuncName = "temporal_diverge";
  StringRef ModuleString = R"(
define amdgpu_kernel void @temporal_diverge(i32 %n, i32 %a, i32 %b) #0 {
; CHECK-NOT: DIVERGENT: br i1 %uni.

entry:
  %tid = call i32 @llvm.amdgcn.workitem.id.x()
  %uni.cond = icmp slt i32 %a, 0
  br label %H

H:
; CHECK-NOT: DIVERGENT: %uni.merge.h
  %uni.merge.h = phi i32 [ 0, %entry ], [ %uni.inc, %H ]
; CHECK-NOT: DIVERGENT: %uni.inc
  %uni.inc = add i32 %uni.merge.h, 1
; CHECK: DIVERGENT: %div.exitx =
  %div.exitx = icmp slt i32 %tid, 0
; CHECK-NOT: DIVERGENT: br i1 %uni.cond,
; don't use the divergent condition yet, this will be updated
  br i1 %uni.cond, label %X, label %H ; divergent branch

X:
; CHECK-NOT: DIVERGENT:  %soon.div.user =
; the way this is right now, this won't be temporally divergent, but once the H exit branch is divergent, it will be
  %soon.div.user = add i32 %uni.inc, 5
  ret void
}
)";

  LLVMContext Context;
  SMDiagnostic Err;
  std::unique_ptr<Module> M = parseAssemblyString(ModuleString, Err, Context);
  ASSERT_TRUE(M) << "Bad LLVM IR as test input? Error: " << Err.getMessage()
                 << "\n---\nLine/Col: " << Err.getLineNo() << "/"
                 << Err.getColumnNo();

  Function *F = M->getFunction(FuncName);

  auto TM =
      createAMDGPUTargetMachine("amdgcn-amd-", "gfx1010", "+wavefrontsize32");
  auto TTI = TM->getTargetTransformInfo(*F);

  auto &BB_X = *--F->end();
  ASSERT_NAME(BB_X, "X");

  auto [_1, _2, Unif] = initiallyComputeUniformityAnalysis(&TTI, F);

  BinaryOperator *soonDivUser = dyn_cast<BinaryOperator>(&*BB_X.begin());
  ASSERT_TRUE(Unif.isUniform(soonDivUser));

  UniformityAnalysisUpdater Updater(Unif);
  // now make the loop exit branch divergent, generating temporal divergence at
  // soonDivUser
  // -> if the sync dependence analysis (SDA) was not up to date, then the
  // replace on the terminator condition would still trigger an
  // `analyzeControlFlowDivergence` call, but the `getJoinBlocks` call inside
  // there would go to the CachedControlDivDescs cache, and wrongly return no
  // join blocks, so no temporal divergence will be propagated. If the SDA works
  // correctly, the join block will be returned and temporal divergence will be
  // propagated, so `soonDivUser` will be marked divergent
  auto soonDivBranch = BB_X.getPrevNode()->getTerminator();
  auto &use = soonDivBranch->getOperandUse(0);
  auto *oldVal = &*use;
  use.set(soonDivBranch->getPrevNode());
  Updater.informAboutRAUW(oldVal, soonDivBranch->getPrevNode());
  EXPECT_DIVERGENT(soonDivUser);

  EXPECT_MATCHES_FRESH_ANALYSIS();
}

TEST(UniformityAnalysisUpdater, Fuzzer) {
  // TODO Implement the fuzzer, although maybe not in this file but in a
  // separate one.
}

TEST(UniformityAnalysisUpdater, GenericRegressionTestComparison) {
  // idea of this test: go through the regression tests for unif analysis, and
  // replace every value with itself, essentially erasing uniforimty info, but
  // keeping control flow in tact
  // -> then check that the resulting analysis matches

  unsigned numFuncs = 0;

  // TODO how do I do this so it works independently of which working dir the
  // tests were started with?
  auto testFilePrefix = "test/Analysis/UniformityAnalysis/AMDGPU/";
  for (auto testFile : {
           "always_uniform.ll",
           "atomics.ll",
           "b42473-r1-crash.ll",
           "branch-after-join.ll",
           "control-flow-intrinsics.ll",
           "hidden_diverge.ll",
           "hidden_loopdiverge.ll",
           "inline-asm.ll",
           "interp_f16.ll",
           "intrinsics.ll",
           "join-at-loop-exit.ll",
           "kernel-args.ll",
           "llvm.amdgcn.buffer.atomic.ll",
           "llvm.amdgcn.image.atomic.ll",
           "no-return-blocks.ll",
           "nodivergencesource.ll",
           "phi-undef.ll",
           "phi_div_branch.ll",
           "phi_div_loop.ll",
           "propagate-loop-live-out.ll",
           "temporal_diverge.ll",
           "trivial-join-at-loop-exit.ll",
           "unreachable-loop-block.ll",
           "unstructured-branch.ll",
           "workitem-intrinsics.ll",
       }) {

    LLVMContext Context;
    SMDiagnostic Err;
    std::unique_ptr<Module> M = llvm::parseIRFile(
        std::string(testFilePrefix) + std::string(testFile), Err, Context);
    ASSERT_TRUE(M) << "Bad LLVM IR as test input? Error: " << Err.getMessage()
                   << "\n---\nLine/Col: " << Err.getLineNo() << "/"
                   << Err.getColumnNo();
    ASSERT_FALSE(verifyModule(*M))
        << "Module verification failed for file " << testFile;
    auto TM =
        createAMDGPUTargetMachine("amdgcn-amd-", "gfx1010", "+wavefrontsize32");

    for (Function &FRef : M->functions()) {
      if (FRef.isDeclaration())
        continue;

      Function *F = &FRef;
      auto TTI = TM->getTargetTransformInfo(*F);

      auto [_1, _2, Unif] = initiallyComputeUniformityAnalysis(&TTI, F);

      UniformityAnalysisUpdater Updater(Unif, &Context);

      // go through all the values except terminators, and replace them with
      // clones of themselves
      for (auto &Inst : llvm::make_early_inc_range(instructions(*F))) {
        if (Inst.isTerminator())
          continue;

        auto [_3, _4, UnifFreshBefore] =
            initiallyComputeUniformityAnalysis(&TTI, F);
        bool WasDivergentBefore = UnifFreshBefore.isDivergent(&Inst);
        EXPECT_EQ(Updater.isDivergent(&Inst), WasDivergentBefore);

        auto *Clone = Inst.clone();
        Clone->setName(Inst.getName());
        IRBuilder(&Inst).Insert(Clone);
        Inst.replaceAllUsesWith(Clone);
        Inst.eraseFromParent();
#define PRINT_DEBUG_POSITION                                                   \
  "file " << testFile << " function " << F->getName() << " replacing "         \
          << *Clone << " with itself"
        LLVM_DEBUG(dbgs() << PRINT_DEBUG_POSITION << "...\n");

        EXPECT_MATCHES_FRESH_ANALYSIS();
#undef PRINT_DEBUG_POSITION
      }
      numFuncs++;
    }
  }

  dbgs() << "Tested " << numFuncs << " functions\n";
}
