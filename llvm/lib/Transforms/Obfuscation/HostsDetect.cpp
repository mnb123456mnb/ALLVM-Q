//===- HostsDetect.cpp - Hosts文件检测注入Pass ----------------===//
//
// 本文件实现Hosts文件检测注入Pass，在程序入口点注入检测代码
// 保留原有逻辑：
//   - 检测 /etc/hosts 中的可疑特征字符串（js/wy/t3/wig）
// 修复与新增：
//   - Android 真实路径 /system/etc/hosts 优先，/etc/hosts 兜底（PC 与安卓都覆盖）
//   - 新增通用劫持检测：任何非注释且不映射 localhost/ip6-localhost/ip6-loopback
//     的行视为 hosts 被修改
//
//===----------------------------------------------------------------------===//
#include "llvm/Transforms/Obfuscation/HostsDetect.h"
#include "llvm/Transforms/Obfuscation/DetectUtils.h"
#include "llvm/Transforms/Obfuscation/ObfuscationPassManager.h"
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
#define DEBUG_TYPE "hostsdetect"
using namespace llvm;
namespace {

struct HostsDetect : public ModulePass {
    static char ID;
    HostsDetect() : ModulePass(ID) {
        initializeHostsDetectPass(*PassRegistry::getPassRegistry());
    }
    StringRef getPassName() const override {
        return {"HostsDetect"};
    }
    bool runOnModule(Module &M) override;
    
    Function* createHostsCheckFunc(Module &M, Function *reportFunc);
};
}
char HostsDetect::ID = 0;

Function* HostsDetect::createHostsCheckFunc(Module &M, Function *reportFunc) {
    LLVMContext &Ctx = M.getContext();
    
    Type *VoidTy = Type::getVoidTy(Ctx);
    Type *Int8Ty = Type::getInt8Ty(Ctx);
    Type *Int32Ty = Type::getInt32Ty(Ctx);
    PointerType *CharPtrTy = PointerType::get(Ctx, 0);
    
    FunctionType *FuncTy = FunctionType::get(VoidTy, {}, false);
    Function *Func = Function::Create(
        FuncTy,
        GlobalValue::InternalLinkage,
        M.getDataLayout().getProgramAddressSpace(),
        "hosts_check",
        &M
    );
    
    Func->addFnAttr(Attribute::NoInline);
    
    BasicBlock *EntryBB = BasicBlock::Create(Ctx, "entry", Func);
    BasicBlock *TrySecondBB = BasicBlock::Create(Ctx, "try_second_path", Func);
    BasicBlock *OpenOkBB = BasicBlock::Create(Ctx, "open_ok", Func);
    BasicBlock *OpenFailBB = BasicBlock::Create(Ctx, "open_fail", Func);
    BasicBlock *LoopBB = BasicBlock::Create(Ctx, "loop", Func);
    BasicBlock *CheckLineBB = BasicBlock::Create(Ctx, "check_line", Func);
    BasicBlock *CheckPatternsBB = BasicBlock::Create(Ctx, "check_patterns", Func);
    BasicBlock *FoundBB = BasicBlock::Create(Ctx, "found", Func);
    BasicBlock *ExitBB = BasicBlock::Create(Ctx, "exit", Func);
    
    IRBuilder<> Builder(EntryBB);
    
    FunctionCallee FopenFunc = M.getOrInsertFunction(
        "fopen",
        FunctionType::get(CharPtrTy, {CharPtrTy, CharPtrTy}, false)
    );
    
    FunctionCallee FgetsFunc = M.getOrInsertFunction(
        "fgets",
        FunctionType::get(CharPtrTy, {CharPtrTy, Int32Ty, CharPtrTy}, false)
    );
    
    FunctionCallee FcloseFunc = M.getOrInsertFunction(
        "fclose",
        FunctionType::get(Int32Ty, {CharPtrTy}, false)
    );
    
    FunctionCallee StrstrFunc = M.getOrInsertFunction(
        "strstr",
        FunctionType::get(CharPtrTy, {CharPtrTy, CharPtrTy}, false)
    );
    
    auto makeString = [&](const char *str) -> Constant* {
        return DetectUtils::createGlobalString(M, str, ".hosts.str");
    };
    
    // 双路径：Android 真实路径优先，PC/Linux 路径兜底
    Constant *HostsPathPrimary = makeString("/system/etc/hosts");
    Constant *HostsPathSecondary = makeString("/etc/hosts");
    Constant *ReadMode = makeString("r");
    
    Value *Fp = Builder.CreateCall(FopenFunc, {HostsPathPrimary, ReadMode});
    Value *FpNull = Builder.CreateICmpEQ(Fp, ConstantPointerNull::get(CharPtrTy));
    Builder.CreateCondBr(FpNull, TrySecondBB, OpenOkBB);
    
    Builder.SetInsertPoint(TrySecondBB);
    Value *Fp2 = Builder.CreateCall(FopenFunc, {HostsPathSecondary, ReadMode});
    Value *Fp2NotNull = Builder.CreateICmpNE(Fp2, ConstantPointerNull::get(CharPtrTy));
    Builder.CreateCondBr(Fp2NotNull, OpenOkBB, OpenFailBB);
    
    Builder.SetInsertPoint(OpenFailBB);
    Builder.CreateBr(ExitBB);
    
    Builder.SetInsertPoint(OpenOkBB);
    
    Type *LineBufTy = ArrayType::get(Int8Ty, 1024);
    Value *LineBuf = Builder.CreateAlloca(LineBufTy, nullptr, "linebuf");
    Value *LineBufPtr = Builder.CreateBitCast(LineBuf, CharPtrTy);
    
    Builder.CreateBr(LoopBB);
    
    Builder.SetInsertPoint(LoopBB);
    
    Value *Line = Builder.CreateCall(FgetsFunc, {LineBufPtr, ConstantInt::get(Int32Ty, 1024), Fp});
    Value *LineNotNull = Builder.CreateICmpNE(Line, ConstantPointerNull::get(CharPtrTy));
    Builder.CreateCondBr(LineNotNull, CheckLineBB, ExitBB);
    
    Builder.SetInsertPoint(CheckLineBB);
    
    Value *FirstChar = Builder.CreateLoad(Int8Ty, LineBufPtr);
    
    Value *IsComment = Builder.CreateICmpEQ(FirstChar, ConstantInt::get(Int8Ty, '#'));
    Value *IsNewline = Builder.CreateICmpEQ(FirstChar, ConstantInt::get(Int8Ty, '\n'));
    Value *IsNull = Builder.CreateICmpEQ(FirstChar, ConstantInt::get(Int8Ty, 0));
    
    Value *Skip = Builder.CreateOr(IsComment, IsNewline);
    Skip = Builder.CreateOr(Skip, IsNull);
    
    Builder.CreateCondBr(Skip, LoopBB, CheckPatternsBB);
    
    Builder.SetInsertPoint(CheckPatternsBB);
    
    // ===== 原有特征（保留） =====
    Constant *LegacyPatterns[] = {
        makeString("js"),
        makeString("wy"),
        makeString("t3"),
        makeString("wig")
    };
    
    Value *LegacyFound = nullptr;
    for (Constant *Pattern : LegacyPatterns) {
        Value *Found = Builder.CreateCall(StrstrFunc, {LineBufPtr, Pattern});
        Value *FoundNotNull = Builder.CreateICmpNE(Found, ConstantPointerNull::get(CharPtrTy));
        if (LegacyFound == nullptr) {
            LegacyFound = FoundNotNull;
        } else {
            LegacyFound = Builder.CreateOr(LegacyFound, FoundNotNull);
        }
    }
    
    // ===== 新增：通用劫持检测 =====
    // 该行命中任何"正常条目"特征 => 安全；否则视为劫持
    Constant *SafePatterns[] = {
        makeString("localhost"),
        makeString("ip6-localhost"),
        makeString("ip6-loopback")
    };
    
    Value *AllSafe = nullptr;
    for (Constant *Pattern : SafePatterns) {
        Value *Found = Builder.CreateCall(StrstrFunc, {LineBufPtr, Pattern});
        Value *FoundNotNull = Builder.CreateICmpNE(Found, ConstantPointerNull::get(CharPtrTy));
        if (AllSafe == nullptr) {
            AllSafe = FoundNotNull;
        } else {
            AllSafe = Builder.CreateOr(AllSafe, FoundNotNull);
        }
    }
    Value *Unsafe = Builder.CreateNot(AllSafe);
    
    // 原特征命中 或 通用劫持命中 => 报告
    Value *ShouldReport = Builder.CreateOr(LegacyFound, Unsafe);
    
    Builder.CreateCondBr(ShouldReport, FoundBB, LoopBB);
    
    Builder.SetInsertPoint(FoundBB);
    Builder.CreateCall(FcloseFunc, {Fp});
    Builder.CreateCall(reportFunc);
    Builder.CreateBr(ExitBB);
    
    Builder.SetInsertPoint(ExitBB);
    Builder.CreateRetVoid();
    
    return Func;
}
bool HostsDetect::runOnModule(Module &M) {
    if (isIRObfuscationDebugEnabled()) {
        errs() << "[DEBUG] HostsDetect: Injecting hosts detection\n";
    }
    Function *MainFunc = M.getFunction("main");
    if (!MainFunc || MainFunc->isDeclaration() || MainFunc->empty()) {
        return false;
    }
    // 使用公共模块创建报告函数
    Function *ReportFunc = DetectUtils::createReportAndKillFunc(M, "Hosts File");
    
    // 创建检测函数
    Function *CheckFunc = createHostsCheckFunc(M, ReportFunc);
    
    // 配置选项
    DetectOptions opts = DetectOptions::create(false);
    
    // 注入到main函数
    return DetectUtils::injectToMain(M, CheckFunc, opts);
}

ModulePass *llvm::createHostsDetectPass() {
    return new HostsDetect();
}
INITIALIZE_PASS_BEGIN(HostsDetect, "hostsdetect", "Inject hosts detection at program start", false, false)
INITIALIZE_PASS_END(HostsDetect, "hostsdetect", "Inject hosts detection at program start", false, false)