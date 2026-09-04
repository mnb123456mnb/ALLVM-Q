//===- UsbProtect.cpp - USB调试禁用注入Pass --------------------===//
//
// 本文件实现USB调试保护注入Pass，在程序入口点注入保护代码
// 检测方式：
//   1. __system_property_get("persist.sys.usb.config") 含 "adb"
//   2. __system_property_get("sys.usb.config") 含 "adb"
//   3. __system_property_get("service.adb.tcp.port") 非空非"0"
//   4. settings global adb_enabled == "1"（system() 兜底）
// 检测到 adb 开启时报告并终止
//
//===----------------------------------------------------------------------===//
#include "llvm/Transforms/Obfuscation/UsbProtect.h"
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
#define DEBUG_TYPE "usbprotect"
using namespace llvm;
namespace {
struct UsbProtect : public ModulePass {
    static char ID;
    UsbProtect() : ModulePass(ID) {
        initializeUsbProtectPass(*PassRegistry::getPassRegistry());
    }
    StringRef getPassName() const override {
        return {"UsbProtect"};
    }
    bool runOnModule(Module &M) override;
    Function* createUsbCheckFunc(Module &M, Function *reportFunc);
};
}
char UsbProtect::ID = 0;

Function* UsbProtect::createUsbCheckFunc(Module &M, Function *reportFunc) {
    LLVMContext &Ctx = M.getContext();

    Type *VoidTy = Type::getVoidTy(Ctx);
    Type *Int8Ty = Type::getInt8Ty(Ctx);
    Type *Int32Ty = Type::getInt32Ty(Ctx);
    PointerType *CharPtrTy = PointerType::get(Ctx, 0);

    FunctionType *FuncTy = FunctionType::get(VoidTy, {}, false);
    Function *Func = Function::Create(
        FuncTy, GlobalValue::InternalLinkage,
        M.getDataLayout().getProgramAddressSpace(),
        "usb_check", &M);
    Func->addFnAttr(Attribute::NoInline);

    // 基础块
    BasicBlock *EntryBB = BasicBlock::Create(Ctx, "entry", Func);
    BasicBlock *CheckProp2BB = BasicBlock::Create(Ctx, "check_prop2", Func);
    BasicBlock *CheckProp3BB = BasicBlock::Create(Ctx, "check_prop3", Func);
    BasicBlock *CheckProp3ValBB = BasicBlock::Create(Ctx, "check_prop3_val", Func);
    BasicBlock *CheckProp4BB0 = BasicBlock::Create(Ctx, "check_prop4", Func);
    BasicBlock *FoundBB = BasicBlock::Create(Ctx, "found", Func);
    BasicBlock *ExitBB = BasicBlock::Create(Ctx, "exit", Func);

    IRBuilder<> Builder(EntryBB);

    FunctionCallee PropGetFunc = M.getOrInsertFunction(
        "__system_property_get",
        FunctionType::get(Int32Ty, {CharPtrTy, CharPtrTy}, false));
    FunctionCallee SystemFunc = M.getOrInsertFunction(
        "system", FunctionType::get(Int32Ty, {CharPtrTy}, false));
    FunctionCallee FopenFunc = M.getOrInsertFunction(
        "fopen", FunctionType::get(CharPtrTy, {CharPtrTy, CharPtrTy}, false));
    FunctionCallee FgetsFunc = M.getOrInsertFunction(
        "fgets", FunctionType::get(CharPtrTy, {CharPtrTy, Int32Ty, CharPtrTy}, false));
    FunctionCallee FcloseFunc = M.getOrInsertFunction(
        "fclose", FunctionType::get(Int32Ty, {CharPtrTy}, false));
    FunctionCallee PopenFunc = M.getOrInsertFunction(
        "popen", FunctionType::get(CharPtrTy, {CharPtrTy, CharPtrTy}, false));
    FunctionCallee PcloseFunc = M.getOrInsertFunction(
        "pclose", FunctionType::get(Int32Ty, {CharPtrTy}, false));
    FunctionCallee StrstrFunc = M.getOrInsertFunction(
        "strstr", FunctionType::get(CharPtrTy, {CharPtrTy, CharPtrTy}, false));
    FunctionCallee StrcmpFunc = M.getOrInsertFunction(
        "strcmp", FunctionType::get(Int32Ty, {CharPtrTy, CharPtrTy}, false));
    FunctionCallee AtoiFunc = M.getOrInsertFunction(
        "atoi", FunctionType::get(Int32Ty, {CharPtrTy}, false));

    auto makeString = [&](const char *str) -> Constant* {
        return DetectUtils::createGlobalString(M, str, ".usb.str");
    };

    Constant *Prop1Name = makeString("persist.sys.usb.config");
    Constant *Prop2Name = makeString("sys.usb.config");
    Constant *Prop3Name = makeString("service.adb.tcp.port");
    Constant *Prop4Name = makeString("init.svc.adbd");
    Constant *NeedleAdb = makeString("adb");
    Constant *NeedleRunning = makeString("running");
    Constant *ZeroStr = makeString("0");
    Constant *SettingsCmd = makeString("settings get global adb_enabled 2>/dev/null");
    Constant *ReadMode = makeString("r");

    Type *Buf92Ty = ArrayType::get(Int8Ty, 92);  // PROP_VALUE_MAX = 92
    Value *Buf = Builder.CreateAlloca(Buf92Ty, nullptr, "propbuf");
    Value *BufPtr = Builder.CreateBitCast(Buf, CharPtrTy);

    // ===== 1. persist.sys.usb.config 含 "adb" =====
    Builder.CreateCall(PropGetFunc, {Prop1Name, BufPtr});
    Value *Found1 = Builder.CreateCall(StrstrFunc, {BufPtr, NeedleAdb});
    Value *Found1NotNull = Builder.CreateICmpNE(Found1, ConstantPointerNull::get(CharPtrTy));
    Builder.CreateCondBr(Found1NotNull, FoundBB, CheckProp2BB);

    // ===== 2. sys.usb.config 含 "adb" =====
    Builder.SetInsertPoint(CheckProp2BB);
    Builder.CreateCall(PropGetFunc, {Prop2Name, BufPtr});
    Value *Found2 = Builder.CreateCall(StrstrFunc, {BufPtr, NeedleAdb});
    Value *Found2NotNull = Builder.CreateICmpNE(Found2, ConstantPointerNull::get(CharPtrTy));
    Builder.CreateCondBr(Found2NotNull, FoundBB, CheckProp3BB);

    // ===== 3. service.adb.tcp.port 非空且非 "0" =====
    Builder.SetInsertPoint(CheckProp3BB);
    Value *Len3 = Builder.CreateCall(PropGetFunc, {Prop3Name, BufPtr});
    Value *Len3Positive = Builder.CreateICmpSGT(Len3, ConstantInt::get(Int32Ty, 0));
    Builder.CreateCondBr(Len3Positive, CheckProp3ValBB, CheckProp4BB0);

    // ===== 3b. 值非 "0" =====
    Builder.SetInsertPoint(CheckProp3ValBB);
    Value *NotZero = Builder.CreateCall(StrcmpFunc, {BufPtr, ZeroStr});
    Value *NotZeroBool = Builder.CreateICmpNE(NotZero, ConstantInt::get(Int32Ty, 0));
    Builder.CreateCondBr(NotZeroBool, FoundBB, CheckProp4BB0);

    // ===== 4. init.svc.adbd == "running" =====
    Builder.SetInsertPoint(CheckProp4BB0);
    Value *Len4 = Builder.CreateCall(PropGetFunc, {Prop4Name, BufPtr});
    Value *Len4Positive = Builder.CreateICmpSGT(Len4, ConstantInt::get(Int32Ty, 0));
    BasicBlock *CheckProp4ValBB = BasicBlock::Create(Ctx, "check_prop4_val", Func);
    BasicBlock *CheckSettings2BB = BasicBlock::Create(Ctx, "check_settings2", Func);
    Builder.CreateCondBr(Len4Positive, CheckProp4ValBB, CheckSettings2BB);

    Builder.SetInsertPoint(CheckProp4ValBB);
    Value *IsRunning = Builder.CreateCall(StrstrFunc, {BufPtr, NeedleRunning});
    Value *IsRunningNotNull = Builder.CreateICmpNE(IsRunning, ConstantPointerNull::get(CharPtrTy));
    Builder.CreateCondBr(IsRunningNotNull, FoundBB, CheckSettings2BB);

    // ===== 5. 兜底: popen("settings get global adb_enabled") == 1 =====
    Builder.SetInsertPoint(CheckSettings2BB);
    Value *Pipe = Builder.CreateCall(PopenFunc, {SettingsCmd, ReadMode});
    Value *PipeNotNull = Builder.CreateICmpNE(Pipe, ConstantPointerNull::get(CharPtrTy));
    BasicBlock *ReadSettingsBB = BasicBlock::Create(Ctx, "read_settings", Func);
    Builder.CreateCondBr(PipeNotNull, ReadSettingsBB, ExitBB);

    Builder.SetInsertPoint(ReadSettingsBB);
    Value *Line = Builder.CreateCall(FgetsFunc, {BufPtr, ConstantInt::get(Int32Ty, 92), Pipe});
    Builder.CreateCall(PcloseFunc, {Pipe});
    Value *LineNotNull = Builder.CreateICmpNE(Line, ConstantPointerNull::get(CharPtrTy));
    BasicBlock *ParseValBB = BasicBlock::Create(Ctx, "parse_val", Func);
    Builder.CreateCondBr(LineNotNull, ParseValBB, ExitBB);

    Builder.SetInsertPoint(ParseValBB);
    Value *EnabledVal = Builder.CreateCall(AtoiFunc, {BufPtr});
    Value *Enabled = Builder.CreateICmpEQ(EnabledVal, ConstantInt::get(Int32Ty, 1));
    Builder.CreateCondBr(Enabled, FoundBB, ExitBB);

    // ===== 发现 adb 开启 =====
    Builder.SetInsertPoint(FoundBB);
    Builder.CreateCall(reportFunc);
    Builder.CreateUnreachable();

    Builder.SetInsertPoint(ExitBB);
    Builder.CreateRetVoid();

    return Func;
}

bool UsbProtect::runOnModule(Module &M) {
    if (isIRObfuscationDebugEnabled()) {
        errs() << "[DEBUG] UsbProtect: Injecting USB protection\n";
    }
    Function *MainFunc = M.getFunction("main");
    if (!MainFunc || MainFunc->isDeclaration() || MainFunc->empty()) {
        return false;
    }
    Function *ReportFunc = DetectUtils::createReportAndKillFunc(M, "USB Debugging");
    Function *CheckFunc = createUsbCheckFunc(M, ReportFunc);
    BasicBlock &EntryBB = MainFunc->getEntryBlock();
    IRBuilder<> Builder(&EntryBB, EntryBB.getFirstInsertionPt());
    Builder.CreateCall(CheckFunc);
    return true;
}
ModulePass *llvm::createUsbProtectPass() {
    return new UsbProtect();
}
INITIALIZE_PASS_BEGIN(UsbProtect, "usbprotect", "Inject USB debug protection at program start", false, false)
INITIALIZE_PASS_END(UsbProtect, "usbprotect", "Inject USB debug protection at program start", false, false)