#ifndef LLVM_ANALYSIS_UNIFORMITYANALYSISUPDATER_H
#define LLVM_ANALYSIS_UNIFORMITYANALYSISUPDATER_H

#include "llvm/ADT/GenericUniformityImpl.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/Analysis/UniformityAnalysis.h"
#include "llvm/IR/ContextCallbacks.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include <memory>

// TODO try to use more forward decls instead of including everything

// TODO It should be explored whether this uniformity analysis updater class can
// be replaced with a lazy uniformity analysis instead
//      Essentially, the updater already does a lazy, point-wise computation of
//      uniformity. The only difference is that, right now, it still depends on
//      a fully-computed analysis at the start. This upfront analysis can most
//      likely be omitted, and transformed into a lazy uniformity analysis
//      (upfront control-flow analysis in the form of CycleInfo and DomTree
//      would still be necessary). For details, as well as a key challenges for
//      the lazy analysis, see "Updatable Uniformity Analysis in LLVM"
//      (https://teichgraeber.digital/files/UpdatableUniformityAnalysisInLLVM.pdf)

// TODO move some of this to the implementation file, instead of defining
// everything inline

namespace llvm {

#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wmacro-redefined"
#define DEBUG_TYPE "unif-analysis-updater"
#pragma clang diagnostic pop
class UniformityAnalysisUpdater {
public:
  // the updater's lifetime is always <= that of the analysis itself, so sharing
  // it via a reference is safe
  UniformityInfo &Info;

private:
  using RAUWCallbackT =
      ContextCallbackOwnershipToken<std::function<void(Value *, Value *)>>;
  using DeleteCallbackT =
      ContextCallbackOwnershipToken<std::function<void(Value *)>>;

  std::optional<RAUWCallbackT> RAUWCallback;
  std::optional<DeleteCallbackT> DeleteCallback;

public:
  // TODO make a nicer API for this, right now this will register callbacks
  // depending on whether it was called with an LLVMContext* or not. Should
  // probably be something like a private 1 argument constructor with only a
  // UniformityInfo, and then use public `CreateAutomaticUpdater` /
  // `CreateManualUpdater` functions or similar.
  explicit UniformityAnalysisUpdater(UniformityInfo &Info,
                                     LLVMContext *Context = nullptr)
      : Info(Info),
        // TODO think about dyn_cast/signature of the callbacks
        RAUWCallback(
            Context ? std::make_optional<RAUWCallbackT>(
                          [&](Value *Old, Value *New) {
                            informAboutRAUW(Old, dyn_cast<Instruction>(New));
                          },
                          Context->pImpl->AfterRAUWCallbacks, *Context->pImpl)
                    : std::nullopt),
        DeleteCallback(Context
                           ? std::make_optional<DeleteCallbackT>(
                                 [&](Value *AboutToDelete) {
                                   informAboutDeletion(
                                       dyn_cast<Instruction>(AboutToDelete));
                                 },
                                 Context->pImpl->BeforeDeleteCallbacks,
                                 *Context->pImpl)
                           : std::nullopt) {}

  /// Informs the updater that a value is about to be deleted.
  /// This should be called *before* the value is really deleted, but once it
  /// already has no uses anymore (see LLVMContextImpl::BeforeDeleteCallbacks).
  void informAboutDeletion(const Instruction *AboutToDelete) {
    assert(AboutToDelete->use_empty() &&
           "only unused instruction deletion supported for now");
    assert(!AboutToDelete->isTerminator() &&
           "terminator/control flow changes not supported for now");

    Info.DA->KnownValues.erase(AboutToDelete);
    Info.DA->UniformOverrides.erase(AboutToDelete);
    // the worklist should always be empty when this is possibly called
    assert(!llvm::is_contained(Info.DA->DivWorklist, AboutToDelete) &&
           "There should be no work going on while a deletion occurs");

    // TODO This needs to erase from the Info.DA->TemporalDivergenceList, but
    // that maybe needs a  different datastructure that's more efficient to
    // iterate through? Do some performance tests to decide this
  }

  /// TODO The API for this should be improved. Even if New is not an
  /// instruction, this should most likely work, probably just by using
  /// `pushUsers` on New to add them to the worklist. Should be called after a
  /// replacement has taken place. Returns a bool which is true iff the
  /// replacement was entirely successful (i.e. no cases that are not handled
  /// occurred). In the future, this should either: a) return void, and all
  /// cases should be handled b) return an enum, to be more explicit about what
  /// the returned value means
  bool informAboutRAUW(const Value *Old, const Instruction *New) {
    assert(!New->isTerminator() &&
           "terminator replacement/control-flow changes not supported yet");

    // 4 basic cases: replacing
    // 1. unif with unif
    // 2. div with div
    // 3. unif with div
    // 4. div with unif
    //
    // 1. and 2. are easy, because nothing changes in the users of the Old/New
    // value
    // 3. is sort of easy, because we can just run the existing divergence
    // propagation seeded only with this one value
    // 4. is hard, because propagating uniformity is not how the current
    // analysis works
    //
    // -> only 1-3 implemented for now
    // TODO idea for 4.: look at all operands of the dependent values of New,
    // and try to propagate their divergence, again keeping track of uniformity
    // candidates

    bool IsOldDivergent = isDivergent(Old);
    bool IsNewDivergent = isDivergent(New);

    LLVM_DEBUG(dbgs() << "old (" << *Old << "): " << IsOldDivergent << " new ("
                      << *New << "): " << IsNewDivergent << "\n");

    // cases 1/2
    if (IsOldDivergent == IsNewDivergent)
      return true;

    // case 3: even though the isDivergent call above might have already
    // propagated this, it is also possible that isDivergent was called before
    // the value was actually replcaed in that case, `isDivergent` above
    // wouldn't have propagated, so we have to explicitly propagate again. This
    // will terminate relatively early in case we've already done it
    if (IsNewDivergent) {
      // put it in the worklist *always*! Even if `New` was already marked
      // divergent before, we still need to reanalyze, because when it was
      // analyzed before, Old might not have been replaced with New yet, so
      // New's divergence might not have been propagated
      Info.DA->DivWorklist.push_back(New);
      Info.DA->propagateSeededWorklistDivergence();
      return true;
    }

    // TODO support case 4 (updating from a divergent to a uniform value). Also
    // see "Updatable Uniformity Analysis in LLVM"
    // (https://teichgraeber.digital/files/UpdatableUniformityAnalysisInLLVM.pdf).
    //      Once case 4 is done, this bool return might also be superfluous.
    // TODO remove the unreachable once it's implemented.
    llvm_unreachable("Divergent -> Uniform replacements not handled yet.");
    return false;
  }

  bool isUniform(const Value *V) { return !isDivergent(V); }

  bool isUniform(const Instruction *I) { return !isDivergent(I); }

  // TODO Info.DA->UniformOverrides are inherently tied to the instruction,
  // meaning that there are basically no real cases in which an update to an
  // existing instruction could change the result of TTI->isAlwaysUniform. But
  // for completeness' sake, it should be possible to register these updates
  // manually with an inform... call, that modifies the analysis'
  // UniformOverrides.
  //      An example of a related case, in which an instruction could be updated
  //      to be a source of divergence, is if the address space of a load is
  //      changed to addrspace 5, which is a source of divergence.

  // TODO Right now, the API of the updater is not super nice, as it replicates
  // the isDivergent/isUniform API of the analysis itself, which is a bit
  // confusing. Once the Updater is replaced with the lazy uniformity analysis,
  // this will be integrated into the analysis itself and the problem will
  // disappear

  bool isDivergent(const Instruction *I) {
    // TODO If/once CFG updates are supported, this needs to be overhauled, as
    // new terminators might result in false checks in DivergentTermBlocks.
    if (I->isTerminator())
      return Info.DA->DivergentTermBlocks.contains(I->getParent());

    return isDivergent(cast<Value>(I));
  }

  /// If the argument V is known, return its known divergence.
  /// If it is not known, compute its divergence from scratch, mimicking and
  /// using the original uniformity analysis for the propagation of value
  /// divergence, as well as control divergence effects.
  bool isDivergent(const Value *V) {
    auto &KnownValues = Info.DA->KnownValues;
    if (auto It = KnownValues.find(V); It != KnownValues.end()) {
      LLVM_DEBUG(dbgs() << "Value " << *V << " is known, divergent: "
                        << (It->second == ValueClassification::DIVERGENT)
                        << "\n");
      return It->second == ValueClassification::DIVERGENT;
    }

    LLVM_DEBUG(dbgs() << "Computing Value " << *V
                      << "'s divergence from scratch...\n");

    // if we don't know it yet, then it's a value that has been inserted
    // -> because RAUWs are tracked explicitly and eagerly, we know that this
    // value isn't used yet (the RAUW will make it be used), so we only have to
    // care about the values that this *uses*, not the values it's *used by*
    // (this is handled in the RAUW callback itself)

    // updates to non-instruction values do not make sense, as arguments don't
    // change, only new ones might be inserted, and those are handled by
    // isAlwaysUniform/isSourceOfDivergence
    assert(isa<Instruction>(V) &&
           "Updates to non-instructions not handled yet");
    const Instruction *Root = dyn_cast<Instruction>(V);

    // Idea to mark :
    // 1. Descend DAG of new nodes in pre-order, keep insert all unknowon nodes
    // as candidates for uniformity, stop at old nodes:
    //    a. If the old node is uniform: stop, we're looking to propagate
    //    divergence, so this doesn't matter. b. If it's divergent, add this
    //    *use* to a list of divergent uses to be propagated.
    // 2. Propagate divergence as usual, possibly overwriting candidates for
    // uniformity.
    //
    // -> At the end, uniform/divergent will be correct, as all candidates for
    // uniformity that didn't have divergence propagated to them are definitely
    // uniform

    // Before we start seeding stuff to propagate, that worklist should be empty
    assert(Info.DA->DivWorklist.empty());

    SmallVector<const Instruction *> OperandWorklist;

    // Returns whether it was marked *divergent* immediately, and thus sibling
    // nodes don't need to be analyzed anymore
    auto AddNewValueToOperandWorklistOrMarkImmediately =
        [&](const Instruction *I) -> bool {
      assert(!Info.DA->KnownValues.contains(I) &&
             "This is only to be called on a new and thus unknown value!");

      // TODO This could be optimized a bit if the TTI implemented a combined
      // `isSourceOfDivergence/isAlwaysUniform` virtual function, which returns
      // an enum of one of the 3 options.
      //      That would eliminate one vfunc call.

      if (Info.DA->TTI->isSourceOfDivergence(I)) {
        LLVM_DEBUG(dbgs() << "  unknown value is source of divergence\n");
        Info.DA->markDivergent(*I);
        // Neither need to analyze the source-of-divergence op's operands, nor
        // the sibling operands
        return true;
      }

      if (Info.DA->TTI->isAlwaysUniform(I)) {
        LLVM_DEBUG(dbgs() << "  unknown value is always uniform\n");
        // We don't want to propagate divergence from operands of this
        // instructions upwards, as an always uniform instruction should stop
        // this propagation
        Info.DA->UniformOverrides.insert(I);
        Info.DA->initiallyMarkUniform(I);
        // Don't need to analyze the always-uniform op's operands (don't add to
        // worklist), but *do* need to further analyze sibling operands, so
        // return false
        return false;
      }

      // It could also be defined in an "AssumedDivergent" cycle -> also
      // (conservatively assumed) divergent in that case
      // TODO Is there a better/more performant way to do this?
      if (!Info.DA->AssumedDivergent.empty() &&
          find_if(Info.DA->AssumedDivergent, [I](auto *Cycle) {
            return Cycle->contains(I->getParent());
          })) {
        Info.DA->markDivergent(*I);
        return true;
      }

      // Otherwise, insert it into the map as "presumed uniform", to possibly be
      // overwritten later
      Info.DA->initiallyMarkUniform(I);

      // Find more new operands
      OperandWorklist.push_back(I);
      // Haven't proved it's divergent, so keep on looking at siblings
      return false;
    };

    AddNewValueToOperandWorklistOrMarkImmediately(Root);

    while (!OperandWorklist.empty()) {
      const Instruction *Cur = OperandWorklist.pop_back_val();
      LLVM_DEBUG(dbgs() << "descended down to unknown value: " << *Cur << "\n");

      for (const auto &OperandUse : Cur->operands()) {
        // Don't explicitly have to check whether we have visited it yet, as
        // this is already handled, because markDivergent
        // AddNewValueToOperandWorklistOrMarkImmediately is only allowed to be
        // called on new values

        // Don't cast it to an instruction yet, arguments are also in the known
        // values map, so check that first

        // TODO The updater needs to materialize all its changes to uniformity
        // analysis before it is destructed. This is theoretically an issue with
        // the implementation as it currently stands, but should be fixed by one
        // of two options:
        // - a) a better API for the updater, that is integrated into the
        // analysis itself (then the analysis itself can always do
        // materializing; in other words: nothing gets lost on destruction,
        // because there is no updater to be destructed)
        // - b) a lazy uniformity analysis as described at the top of this file,
        // as it would also integrate the updater.
        //
        // Choosing one of these options is most likely desirable and should be
        // done before upstreaming. However, if this is not done, one other
        // option would be to omit most, if not all, of the
        // continue/continueWhile statements here (which are essentially early
        // exits in traversal), as that would also fully traverse the data-flow
        // DAG upon replacement, materializing the updates.

        const Instruction *OperandInstr = nullptr;

        // as the loop modifies KnownValues with insertions, check the newest
        // .end() operator here every time
        if (auto It = KnownValues.find(OperandUse); It != KnownValues.end()) {
          // if it's divergent, add this value to the tracking set; basically
          // doing `pushUsers` for only this one user of `It`
          if (It->second == ValueClassification::DIVERGENT) {
            LLVM_DEBUG(dbgs() << "  marked unknown value divergent because of "
                                 "divergent operand: "
                              << *OperandUse << "\n");
            Info.DA->markDivergent(*Cur);
            // break from the for loop of the operands: we just want to compute
            // this value's uniformity, we don't necessarily need to eagerly
            // analyze the entire operand DAG for that
            // TODO maybe have a setting/mode of the updater that *does* do that
            goto continueWhile;
          }
        } else if ((OperandInstr = dyn_cast<Instruction>(OperandUse))) {
          // In this case we're at another new node, so again either add it to
          // the list, or directly mark it.
          // -> If it's *not* in the KnownValues, then it's only relevant to us
          // if it is an instruction, arguments are caught by
          // isAlwaysUniform/isSourceOfDivergence

          bool MarkedDivergent =
              AddNewValueToOperandWorklistOrMarkImmediately(OperandInstr);
          if (MarkedDivergent) {
            // no need to analyze more operands of Cur
            goto continueWhile;
          }
        }

        // at this point, we know it is either known uniform, or unknown. But
        // even if it's known uniform, this might still be a temporally
        // divergent use

        // if it's not an instruction, it cannot be a temporally divergent use
        if (!OperandInstr) {
          // try to cast it to an instruction
          OperandInstr = dyn_cast<Instruction>(OperandUse);
          if (!OperandInstr)
            continue;

          // TODO maybe remove comment
          // this if is the same as:
          // if(!OperandInstr && !(OperandInstr =
          // dyn_cast<Instruction>(OperandUse)))
          //   continue;
        }

        // conservative pre-check/guard to check for temporal divergence less
        // often: (if they share the same parent (technically even if they share
        // the same lowest-level loop), there cannot be temporal divergence)
        if (OperandInstr->getParent() == Cur->getParent())
          continue;

        // TODO another option to reduce the amount of temporal divergence
        // checks would be to check for temporal divergence on a separate
        // iteration over the operands; that would make "normal" divergence
        // propagate first, possibly saving some temporal divergence checks.
        // Test whether this is worth it in terms of performance
        if (auto CycleCausingTempDiv = Info.DA->getTemporallyDivergentCycle(
                *Cur->getParent(), *OperandInstr)) {
          LLVM_DEBUG(dbgs() << "  unknown value uses value " << *OperandUse
                            << " in a temporally divergent way\n");
          Info.DA->markDivergent(*Cur);
          // TODO test that this is correct
          Info.DA->recordTemporalDivergence(OperandInstr, Cur,
                                            CycleCausingTempDiv);
          goto continueWhile;
        }
      }

      // if we got here, it's not divergent from the operands alone
      // but it might still be a PHI of a join block of a divergent path!
      if (const auto *Phi = dyn_cast<PHINode>(Cur)) {
        // mirroring `taintAndPushPhiNodes`
        // TODO this is a bit of code duplication right now, but once this has
        // become the lazy uniformity analysis, this should be merged into one
        // method again
        if (SSAContext::isConstantOrUndefValuePhi(*Phi))
          goto continueWhile;

        // problem: we might be *at* a join block, but the actual SDA only
        // operates the other way round: from the divergent branch to the join
        // block best shot we have: because we don't allow CFG modifications,
        // the `CachedControlDivDescs` already contains an up-to-date mapping of
        // diverging branches to join blocks
        // -> search the entries of that

        // TODO this needs to be a linear search right now, test if it's worth
        // it to cache this in the opposite direction with a second map during
        // construction (mapping join blocks to their diverging branches), and
        // then do a lookup

        for (auto &Entry : Info.DA->SDA.CachedControlDivDescs) {
          // TODO maybe remove comment
          // can't iterate over .values(), as that calls a deleted unique_ptr
          // constructor
          auto &JoinBlockSet = Entry.second->JoinDivBlocks;

          LLVM_DEBUG(
              dbgs() << "Cached control divergence: diverged path starts at '"
                     << Entry.first->getName() << "';\n";
              for (auto *JoinBlock
                   : JoinBlockSet) dbgs()
              << "  joins at: '" << JoinBlock->getName() << "'\n";);

          if (JoinBlockSet.contains(Phi->getParent())) {
            // this is a phi on a join block of a divergent branch -> mark
            // divergent
            LLVM_DEBUG(
                dbgs()
                << "PHI parent block '" << Phi->getParent()->getName()
                << "' is join node of divergent path! Marking divergent...\n");
            Info.DA->markDivergent(*Phi);
            goto continueWhile;
          }
        }
      }
      // no tiered break/continue statements
    continueWhile:;
    }

    Info.DA->propagateSeededWorklistDivergence();

    assert(Info.DA->KnownValues.contains(V) &&
           "Didn't actually compute inserted value's divergence");
    LLVM_DEBUG(
        dbgs() << "...value " << *V
               << "'s divergence was computed from scratch! Divergent: "
               << (Info.DA->KnownValues[V] == ValueClassification::DIVERGENT)
               << "\n");
    // basically just go back to the start
    return isDivergent(V);
  }
};
#undef DEBUG_TYPE

} // namespace llvm

#endif // LLVM_ANALYSIS_UNIFORMITYANALYSISUPDATER_H
