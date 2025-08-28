#include "llvm/Analysis/UniformityAnalysisUpdater.h"

// TODO fix includes

#include "llvm/ADT/GenericUniformityImpl.h"
#include "llvm/Analysis/CycleAnalysis.h"
#include "llvm/Analysis/DomTreeUpdater.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/Analysis/UniformityAnalysis.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/InitializePasses.h"

using namespace llvm;

namespace llvm {} // namespace llvm
