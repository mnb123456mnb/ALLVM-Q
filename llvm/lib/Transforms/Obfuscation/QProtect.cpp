//===- QProtect.cpp - Q-Protector注入Pass ----------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// Q-Protector 输出注入 Pass
// 注入到全局构造函数，避免与VMProtect冲突
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Obfuscation/QProtect.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include <vector>
#define DEBUG_TYPE "qprotect"

using namespace llvm;

namespace {

struct QProtect : public ModulePass {
    static char ID;

    QProtect() : ModulePass(ID) {
        initializeQProtectPass(*PassRegistry::getPassRegistry());
    }

    StringRef getPassName() const override {
        return {"QProtect"};
    }

    bool runOnModule(Module &M) override;
};

}

char QProtect::ID = 0;

bool QProtect::runOnModule(Module &M) {
    // 单模块守卫：只在包含 main 的编译单元注入启动水印，
    // 避免多文件工程每个 .cpp 各打一遍横幅刷屏
    if (!M.getFunction("main"))
        return true;
    // 全局去重：VMP 会把 main 提取到独立 Module，导致两个模块都含 main；
    // 用静态标志保证整个编译进程只注入一份水印
    static bool s_watermarkInjected = false;
    if (s_watermarkInjected)
        return true;
    s_watermarkInjected = true;
    LLVMContext &Ctx = M.getContext();
    Type *Int32Ty = Type::getInt32Ty(Ctx);
    Type *CharPtrTy = PointerType::get(Ctx, 0);
    Type *VoidTy = Type::getVoidTy(Ctx);

    // 创建QProtect初始化函数
    FunctionType *InitFuncTy = FunctionType::get(VoidTy, false);
    Function *InitFunc = Function::Create(
        InitFuncTy, GlobalValue::PrivateLinkage, ".ap.init", &M);
    
    BasicBlock *InitBB = BasicBlock::Create(Ctx, "entry", InitFunc);
    IRBuilder<> Builder(InitBB);

    // 声明外部函数
    FunctionCallee PrintfFunc = M.getOrInsertFunction(
        "printf", FunctionType::get(Int32Ty, {CharPtrTy}, true));

    // 打印 Q-Protector 标识
    Constant *QProtectStr = ConstantDataArray::getString(Ctx, "\x1b[38;2;65;179;73mQ-Protector\x1b[0m\n");
    GlobalVariable *QProtectGV = new GlobalVariable(
        M, QProtectStr->getType(), true, GlobalValue::PrivateLinkage,
        QProtectStr, ".ap.str");
    Constant *QProtectPtr = ConstantExpr::getBitCast(QProtectGV, CharPtrTy);
    Builder.CreateCall(PrintfFunc, {QProtectPtr});

    // 打印版本号
    Constant *VersionStr = ConstantDataArray::getString(Ctx, "\x1b[38;2;65;179;73mversion: 1.0.0\x1b[0m\n");
    GlobalVariable *VersionGV = new GlobalVariable(
        M, VersionStr->getType(), true, GlobalValue::PrivateLinkage,
        VersionStr, ".ap.version");
    Constant *VersionPtr = ConstantExpr::getBitCast(VersionGV, CharPtrTy);
    Builder.CreateCall(PrintfFunc, {VersionPtr});
    
    Builder.CreateRetVoid();

    // 将初始化函数添加到全局构造函数列表
    // 使用优先级65535确保在其他构造函数之后执行
    StructType *CtorTy = StructType::get(Ctx, {Int32Ty, CharPtrTy, CharPtrTy});
    
    Constant *CtorFuncPtr = ConstantExpr::getBitCast(InitFunc, CharPtrTy);
    Constant *Priority = ConstantInt::get(Int32Ty, 65535);
    Constant *CtorElem = ConstantStruct::get(CtorTy, {Priority, CtorFuncPtr, 
        ConstantPointerNull::get(PointerType::get(Ctx, 0))});
    
    // 查找或创建llvm.global_ctors
    GlobalVariable *GlobalCtors = M.getGlobalVariable("llvm.global_ctors");
    if (!GlobalCtors) {
        GlobalCtors = new GlobalVariable(
            M, ArrayType::get(CtorTy, 1), false,
            GlobalValue::AppendingLinkage,
            ConstantArray::get(ArrayType::get(CtorTy, 1), {CtorElem}),
            "llvm.global_ctors");
    } else {
        // 追加到现有的构造函数列表
        Constant *OldInit = GlobalCtors->getInitializer();
        ArrayType *OldArrTy = cast<ArrayType>(OldInit->getType());
        unsigned OldSize = OldArrTy->getNumElements();
        
        ArrayType *NewArrTy = ArrayType::get(CtorTy, OldSize + 1);
        std::vector<Constant *> NewCtors;
        for (unsigned i = 0; i < OldSize; ++i) {
            NewCtors.push_back(OldInit->getAggregateElement(i));
        }
        NewCtors.push_back(CtorElem);
        
        GlobalCtors->setInitializer(ConstantArray::get(NewArrTy, NewCtors));
    }

    return true;
}

ModulePass *llvm::createQProtectPass() {
    return new QProtect();
}

INITIALIZE_PASS_BEGIN(QProtect, "qprotect", "Inject Q-Protector output at program start", false, false)
INITIALIZE_PASS_END(QProtect, "qprotect", "Inject Q-Protector output at program start", false, false)
