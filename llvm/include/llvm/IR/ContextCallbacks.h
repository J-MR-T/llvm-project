#ifndef LLVM_IR_CONTEXTCALLBACKS_H
#define LLVM_IR_CONTEXTCALLBACKS_H

// TODO Find a better file layout/solution to this.
//      One option would be to expose accessors in the real LLVMContext, not the Impl. Then LLVMcontext.cpp could access the underlying things in LLVMContextImpl.h
#include "../lib/IR/LLVMContextImpl.h"

#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/Value.h"
#include <functional>
#include <llvm/IR/LLVMContext.h>

using namespace llvm;

namespace llvm {
// TODO name
template<typename ContextCallbackFnTy>
class ContextCallbackOwnershipToken {
    static_assert(std::is_void_v<typename ContextCallbackFnTy::result_type>, "Callback return type needs to be void");
protected:
    // TODO theres an implicit assumption here that the context doesnt get moved or similar in between
    LLVMContextImpl& ContextImpl;
    // TODO name
    SmallVector<ContextCallbackOwnershipToken*>& RegisteredWithThis;

    ContextCallbackFnTy RegisteredCallback;

public:

    ContextCallbackOwnershipToken(ContextCallbackFnTy&& Callback, SmallVector<ContextCallbackOwnershipToken*>& RegisterWithThis, LLVMContextImpl& ContextImpl) : ContextImpl(ContextImpl), RegisteredWithThis(RegisterWithThis), RegisteredCallback(std::move(Callback)){
        RegisterWithThis.push_back(this);
        ContextImpl.HasCallbacks = true;
    }

    ~ContextCallbackOwnershipToken(){
        // remove itself from the list
        for(auto It = RegisteredWithThis.begin(), E = RegisteredWithThis.end(); It != E; ++It){
            if(*It == this){
                RegisteredWithThis.erase(It);
                // TODO The current solution directly depends on the internals of the context, is there a better one?
                if(ContextImpl.AfterRAUWCallbacks.empty() && ContextImpl.BeforeDeleteCallbacks.empty())
                    ContextImpl.HasCallbacks = false;
                return;
            }
        }

        llvm_unreachable("Registered ContextCallback was deregistered before destructor");
    }

    // move ctor/assignment
    // TODO theoretically, this could be allowed. The class has exclusive ownership semantics after all
    //      but in practice, there shouldn't really be a reason to use this; while the implementation would be tricky and bug-prone
    ContextCallbackOwnershipToken(ContextCallbackOwnershipToken&& Other) = delete;
    ContextCallbackOwnershipToken& operator=(ContextCallbackOwnershipToken&& Other) = delete;
    // copy ctor/assignment
    ContextCallbackOwnershipToken(const ContextCallbackOwnershipToken& Other) = delete;
    const ContextCallbackOwnershipToken& operator=(const ContextCallbackOwnershipToken& Other) = delete;
   
    template<typename... Args>
    void operator()(Args... args){
        RegisteredCallback(args...);
    }
};

} // namespace llvm

#endif  // LLVM_IR_CONTEXTCALLBACKS_H
