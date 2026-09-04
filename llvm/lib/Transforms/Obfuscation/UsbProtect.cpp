//===- UsbProtect.cpp - USB调试禁用注入Pass --------------------===//
//
// 本文件实现USB调试保护注入Pass，在程序入口点注入保护代码
// 保留原有逻辑：
//   - 尝试写 /sys/class/android_usb/android0/enable=0、functions=none
//   - setprop 关闭 usb 配置
//   - 读回 enable/functions 判断是否仍开启
// 新增检测（修复现代设备检测失效）：
//   - __system_property_get("persist.sys.usb.config") 含 "adb"
//   - __system_property_get("sys.usb.config") 含 "adb"
//   - __system_property_get("init.svc.adbd") == "running"
//   - popen("settings get global adb_enabled") == 1 兜底
// 检测到 adb 仍开启时报告并终止
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
    Type *Int64Ty = Type::getInt64Ty(Ctx);
    PointerType *CharPtrTy = PointerType::get(Ctx, 0);

    FunctionType *FuncTy = FunctionType::get(VoidTy, {}, false);
    Function *Func = Function::Create(
        FuncTy, GlobalValue::InternalLinkage,
        M.getDataLayout().getProgramAddressSpace(),
        "usb_check", &M);
    Func->addFnAttr(Attribute::NoInline);

    // ===== 块定义 =====
    // 原有逻辑
    BasicBlock *EntryBB = BasicBlock::Create(Ctx, "entry", Func);
    BasicBlock *WriteEnableBB = BasicBlock::Create(Ctx, "write_enable", Func);
    BasicBlock *SkipEnableBB = BasicBlock::Create(Ctx, "skip_enable", Func);
    BasicBlock *WriteFuncsBB = BasicBlock::Create(Ctx, "write_funcs", Func);
    BasicBlock *SkipFuncsBB = BasicBlock::Create(Ctx, "skip_funcs", Func);
    BasicBlock *CheckEnableBB = BasicBlock::Create(Ctx, "check_enable", Func);
    BasicBlock *CheckEnableOkBB = BasicBlock::Create(Ctx, "check_enable_ok", Func);
    BasicBlock *CheckFuncsBB = BasicBlock::Create(Ctx, "check_funcs", Func);
    BasicBlock *CheckFuncsOkBB = BasicBlock::Create(Ctx, "check_funcs_ok", Func);
    // 新增检测
    BasicBlock *CheckProp1BB = BasicBlock::Create(Ctx, "check_prop1", Func);
    BasicBlock *CheckProp2BB = BasicBlock::Create(Ctx, "check_prop2", Func);
    BasicBlock *CheckProp4BB = BasicBlock::Create(Ctx, "check_prop4", Func);
    BasicBlock *CheckProp4ValBB = BasicBlock::Create(Ctx, "check_prop4_val", Func);
    BasicBlock *CheckSettingsBB = BasicBlock::Create(Ctx, "check_settings", Func);
    BasicBlock *ReadSettingsBB = BasicBlock::Create(Ctx, "read_settings", Func);
    BasicBlock *ParseValBB = BasicBlock::Create(Ctx, "parse_val", Func);
    BasicBlock *FoundBB = BasicBlock::Create(Ctx, "found", Func);
    BasicBlock *ExitBB = BasicBlock::Create(Ctx, "exit", Func);

    IRBuilder<> Builder(EntryBB);

    FunctionCallee FopenFunc = M.getOrInsertFunction(
        "fopen", FunctionType::get(CharPtrTy, {CharPtrTy, CharPtrTy}, false));
    FunctionCallee FwriteFunc = M.getOrInsertFunction(
        "fwrite", FunctionType::get(Int64Ty, {CharPtrTy, Int64Ty, Int64Ty, CharPtrTy}, false));
    FunctionCallee FreadFunc = M.getOrInsertFunction(
        "fread", FunctionType::get(Int64Ty, {CharPtrTy, Int64Ty, Int64Ty, CharPtrTy}, false));
    FunctionCallee FgetsFunc = M.getOrInsertFunction(
        "fgets", FunctionType::get(CharPtrTy, {CharPtrTy, Int32Ty, CharPtrTy}, false));
    FunctionCallee FcloseFunc = M.getOrInsertFunction(
        "fclose", FunctionType::get(Int32Ty, {CharPtrTy}, false));
    FunctionCallee SystemFunc = M.getOrInsertFunction(
        "system", FunctionType::get(Int32Ty, {CharPtrTy}, false));
    FunctionCallee PopenFunc = M.getOrInsertFunction(
        "popen", FunctionType::get(CharPtrTy, {CharPtrTy, CharPtrTy}, false));
    FunctionCallee PcloseFunc = M.getOrInsertFunction(
        "pclose", FunctionType::get(Int32Ty, {CharPtrTy}, false));
    FunctionCallee UsleepFunc = M.getOrInsertFunction(
        "usleep", FunctionType::get(Int32Ty, {Int32Ty}, false));
    FunctionCallee StrstrFunc = M.getOrInsertFunction(
        "strstr", FunctionType::get(CharPtrTy, {CharPtrTy, CharPtrTy}, false));
    FunctionCallee StrcmpFunc = M.getOrInsertFunction(
        "strcmp", FunctionType::get(Int32Ty, {CharPtrTy, CharPtrTy}, false));
    FunctionCallee AtoiFunc = M.getOrInsertFunction(
        "atoi", FunctionType::get(Int32Ty, {CharPtrTy}, false));
    FunctionCallee PropGetFunc = M.getOrInsertFunction(
        "__system_property_get",
        FunctionType::get(Int32Ty, {CharPtrTy, CharPtrTy}, false));

    auto makeString = [&](const char *str) -> Constant* {
        return DetectUtils::createGlobalString(M, str, ".usb.str");
    };

    // 原有字符串
    Constant *WriteMode = makeString("w");
    Constant *ReadMode = makeString("r");
    Constant *EnablePath = makeString("/sys/class/android_usb/android0/enable");
    Constant *FuncsPath = makeString("/sys/class/android_usb/android0/functions");
    Constant *Str0 = makeString("0");
    Constant *StrNone = makeString("none");
    Constant *SetpropCmd1 = makeString("setprop sys.usb.config none 2>/dev/null");
    Constant *SetpropCmd2 = makeString("setprop sys.usb.state none 2>/dev/null");
    Constant *SetpropCmd3 = makeString("setprop persist.sys.usb.config none 2>/dev/null");
    Constant *Needle1 = makeString("1");
    Constant *NeedleMtp = makeString("mtp");
    Constant *NeedlePtp = makeString("ptp");
    Constant *NeedleMass = makeString("mass_storage");
    Constant *NeedleFile = makeString("file");
    // 新增字符串
    Constant *Prop1Name = makeString("persist.sys.usb.config");
    Constant *Prop2Name = makeString("sys.usb.config");
    Constant *Prop4Name = makeString("init.svc.adbd");
    Constant *NeedleAdb = makeString("adb");
    Constant *NeedleRunning = makeString("running");
    Constant *ZeroStr = makeString("0");
    Constant *SettingsCmd = makeString("settings get global adb_enabled 2>/dev/null");

    Type *Buf16Ty = ArrayType::get(Int8Ty, 16);
    Value *Buf16 = Builder.CreateAlloca(Buf16Ty, nullptr, "buf16");
    Value *Buf16Ptr = Builder.CreateBitCast(Buf16, CharPtrTy);
    Type *Buf256Ty = ArrayType::get(Int8Ty, 256);
    Value *Buf256 = Builder.CreateAlloca(Buf256Ty, nullptr, "buf256");
    Value *Buf256Ptr = Builder.CreateBitCast(Buf256, CharPtrTy);

    // ================= 原有逻辑：尝试关闭 USB =================
    Value *Fp = Builder.CreateCall(FopenFunc, {EnablePath, WriteMode});
    Value *FpNotNull = Builder.CreateICmpNE(Fp, ConstantPointerNull::get(CharPtrTy));
    Builder.CreateCondBr(FpNotNull, WriteEnableBB, SkipEnableBB);

    Builder.SetInsertPoint(WriteEnableBB);
    Builder.CreateCall(FwriteFunc, {Str0, ConstantInt::get(Int64Ty, 1), ConstantInt::get(Int64Ty, 1), Fp});
    Builder.CreateCall(FcloseFunc, {Fp});
    Builder.CreateBr(SkipEnableBB);

    Builder.SetInsertPoint(SkipEnableBB);
    Fp = Builder.CreateCall(FopenFunc, {FuncsPath, WriteMode});
    FpNotNull = Builder.CreateICmpNE(Fp, ConstantPointerNull::get(CharPtrTy));
    Builder.CreateCondBr(FpNotNull, WriteFuncsBB, SkipFuncsBB);

    Builder.SetInsertPoint(WriteFuncsBB);
    Builder.CreateCall(FwriteFunc, {StrNone, ConstantInt::get(Int64Ty, 1), ConstantInt::get(Int64Ty, 4), Fp});
    Builder.CreateCall(FcloseFunc, {Fp});
    Builder.CreateBr(SkipFuncsBB);

    Builder.SetInsertPoint(SkipFuncsBB);
    Builder.CreateCall(SystemFunc, {SetpropCmd1});
    Builder.CreateCall(SystemFunc, {SetpropCmd2});
    Builder.CreateCall(SystemFunc, {SetpropCmd3});
    Builder.CreateCall(UsleepFunc, {ConstantInt::get(Int32Ty, 500000)});
    Builder.CreateBr(CheckEnableBB);

    // ================= 原有逻辑：读回 sysfs 判断 =================
    Builder.SetInsertPoint(CheckEnableBB);
    Fp = Builder.CreateCall(FopenFunc, {EnablePath, ReadMode});
    FpNotNull = Builder.CreateICmpNE(Fp, ConstantPointerNull::get(CharPtrTy));
    // 如果文件不存在，跳过 sysfs 检测，进入新增属性检测
    Builder.CreateCondBr(FpNotNull, CheckEnableOkBB, CheckProp1BB);

    Builder.SetInsertPoint(CheckEnableOkBB);
    Builder.CreateCall(FreadFunc, {Buf16Ptr, ConstantInt::get(Int64Ty, 1), ConstantInt::get(Int64Ty, 15), Fp});
    Builder.CreateCall(FcloseFunc, {Fp});
    Value *Found1 = Builder.CreateCall(StrstrFunc, {Buf16Ptr, Needle1});
    Value *Found1NotNull = Builder.CreateICmpNE(Found1, ConstantPointerNull::get(CharPtrTy));
    Builder.CreateCondBr(Found1NotNull, FoundBB, CheckFuncsBB);

    Builder.SetInsertPoint(CheckFuncsBB);
    Fp = Builder.CreateCall(FopenFunc, {FuncsPath, ReadMode});
    FpNotNull = Builder.CreateICmpNE(Fp, ConstantPointerNull::get(CharPtrTy));
    // 文件不存在也进入新增属性检测
    Builder.CreateCondBr(FpNotNull, CheckFuncsOkBB, CheckProp1BB);

    Builder.SetInsertPoint(CheckFuncsOkBB);
    Builder.CreateCall(FreadFunc, {Buf256Ptr, ConstantInt::get(Int64Ty, 1), ConstantInt::get(Int64Ty, 255), Fp});
    Builder.CreateCall(FcloseFunc, {Fp});
    Value *FoundMtp = Builder.CreateCall(StrstrFunc, {Buf256Ptr, NeedleMtp});
    Value *FoundMtpNotNull = Builder.CreateICmpNE(FoundMtp, ConstantPointerNull::get(CharPtrTy));
    Value *FoundPtp = Builder.CreateCall(StrstrFunc, {Buf256Ptr, NeedlePtp});
    Value *FoundPtpNotNull = Builder.CreateICmpNE(FoundPtp, ConstantPointerNull::get(CharPtrTy));
    Value *FoundMass = Builder.CreateCall(StrstrFunc, {Buf256Ptr, NeedleMass});
    Value *FoundMassNotNull = Builder.CreateICmpNE(FoundMass, ConstantPointerNull::get(CharPtrTy));
    Value *FoundFile = Builder.CreateCall(StrstrFunc, {Buf256Ptr, NeedleFile});
    Value *FoundFileNotNull = Builder.CreateICmpNE(FoundFile, ConstantPointerNull::get(CharPtrTy));
    Value *AnyFound = Builder.CreateOr(FoundMtpNotNull, FoundPtpNotNull);
    AnyFound = Builder.CreateOr(AnyFound, FoundMassNotNull);
    AnyFound = Builder.CreateOr(AnyFound, FoundFileNotNull);
    // 传输模式开启 => 报告；否则继续新增属性检测
    Builder.CreateCondBr(AnyFound, FoundBB, CheckProp1BB);

    // ================= 新增检测 1: persist.sys.usb.config 含 "adb" =================
    Builder.SetInsertPoint(CheckProp1BB);
    Builder.CreateCall(PropGetFunc, {Prop1Name, Buf256Ptr});
    Value *FoundAdb1 = Builder.CreateCall(StrstrFunc, {Buf256Ptr, NeedleAdb});
    Value *FoundAdb1NotNull = Builder.CreateICmpNE(FoundAdb1, ConstantPointerNull::get(CharPtrTy));
    Builder.CreateCondBr(FoundAdb1NotNull, FoundBB, CheckProp2BB);

    // ================= 新增检测 2: sys.usb.config 含 "adb" =================
    Builder.SetInsertPoint(CheckProp2BB);
    Builder.CreateCall(PropGetFunc, {Prop2Name, Buf256Ptr});
    Value *FoundAdb2 = Builder.CreateCall(StrstrFunc, {Buf256Ptr, NeedleAdb});
    Value *FoundAdb2NotNull = Builder.CreateICmpNE(FoundAdb2, ConstantPointerNull::get(CharPtrTy));
    Builder.CreateCondBr(FoundAdb2NotNull, FoundBB, CheckProp4BB);

    // ================= 新增检测 3: init.svc.adbd == "running" =================
    Builder.SetInsertPoint(CheckProp4BB);
    Value *Len4 = Builder.CreateCall(PropGetFunc, {Prop4Name, Buf256Ptr});
    Value *Len4Positive = Builder.CreateICmpSGT(Len4, ConstantInt::get(Int32Ty, 0));
    Builder.CreateCondBr(Len4Positive, CheckProp4ValBB, CheckSettingsBB);

    Builder.SetInsertPoint(CheckProp4ValBB);
    Value *IsRunning = Builder.CreateCall(StrstrFunc, {Buf256Ptr, NeedleRunning});
    Value *IsRunningNotNull = Builder.CreateICmpNE(IsRunning, ConstantPointerNull::get(CharPtrTy));
    Builder.CreateCondBr(IsRunningNotNull, FoundBB, CheckSettingsBB);

    // ================= 新增检测 4: settings adb_enabled == 1 兜底 =================
    Builder.SetInsertPoint(CheckSettingsBB);
    Value *Pipe = Builder.CreateCall(PopenFunc, {SettingsCmd, ReadMode});
    Value *PipeNotNull = Builder.CreateICmpNE(Pipe, ConstantPointerNull::get(CharPtrTy));
    Builder.CreateCondBr(PipeNotNull, ReadSettingsBB, ExitBB);

    Builder.SetInsertPoint(ReadSettingsBB);
    Value *Line = Builder.CreateCall(FgetsFunc, {Buf16Ptr, ConstantInt::get(Int32Ty, 16), Pipe});
    Builder.CreateCall(PcloseFunc, {Pipe});
    Value *LineNotNull = Builder.CreateICmpNE(Line, ConstantPointerNull::get(CharPtrTy));
    Builder.CreateCondBr(LineNotNull, ParseValBB, ExitBB);

    Builder.SetInsertPoint(ParseValBB);
    Value *EnabledVal = Builder.CreateCall(AtoiFunc, {Buf16Ptr});
    Value *Enabled = Builder.CreateICmpEQ(EnabledVal, ConstantInt::get(Int32Ty, 1));
    Builder.CreateCondBr(Enabled, FoundBB, ExitBB);

    // ================= 发现 USB 调试开启 =================
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