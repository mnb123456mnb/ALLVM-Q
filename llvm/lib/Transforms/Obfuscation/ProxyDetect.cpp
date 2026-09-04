//===- ProxyDetect.cpp - 代理检测注入Pass ---------------------===//
//
// 本文件实现代理检测注入Pass，在程序入口点注入检测代码
// 检测方式：
//   1. 环境变量 http_proxy / HTTP_PROXY / https_proxy / HTTPS_PROXY / all_proxy
//   2. Android 系统属性 http.proxy / global.http_proxy / global_http_proxy_*
//   3. popen("settings get global http_proxy") 兜底
//
//===----------------------------------------------------------------------===//
#include "llvm/Transforms/Obfuscation/ProxyDetect.h"
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
#define DEBUG_TYPE "proxydetect"
using namespace llvm;
namespace {

struct ProxyDetect : public ModulePass {
    static char ID;
    ProxyDetect() : ModulePass(ID) {
        initializeProxyDetectPass(*PassRegistry::getPassRegistry());
    }
    StringRef getPassName() const override {
        return {"ProxyDetect"};
    }
    bool runOnModule(Module &M) override;
    Function* createProxyCheckFunc(Module &M, Function *reportFunc);
};
}
char ProxyDetect::ID = 0;

Function* ProxyDetect::createProxyCheckFunc(Module &M, Function *reportFunc) {
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
        "proxy_check",
        &M
    );

    Func->addFnAttr(Attribute::NoInline);

    BasicBlock *EntryBB = BasicBlock::Create(Ctx, "entry", Func);
    BasicBlock *CheckHttpProxyBB = BasicBlock::Create(Ctx, "check_http_proxy", Func);
    BasicBlock *CheckHttpsProxyBB = BasicBlock::Create(Ctx, "check_https_proxy", Func);
    BasicBlock *CheckAllProxyBB = BasicBlock::Create(Ctx, "check_all_proxy", Func);
    BasicBlock *CheckProp1BB = BasicBlock::Create(Ctx, "check_prop1", Func);
    BasicBlock *CheckProp2BB = BasicBlock::Create(Ctx, "check_prop2", Func);
    BasicBlock *CheckProp3BB = BasicBlock::Create(Ctx, "check_prop3", Func);
    BasicBlock *CheckProp4BB = BasicBlock::Create(Ctx, "check_prop4", Func);
    BasicBlock *CheckSettingsBB = BasicBlock::Create(Ctx, "check_settings", Func);
    BasicBlock *ReadSettingsBB = BasicBlock::Create(Ctx, "read_settings", Func);
    BasicBlock *ParseValBB = BasicBlock::Create(Ctx, "parse_val", Func);
    BasicBlock *FoundProxyBB = BasicBlock::Create(Ctx, "found_proxy", Func);
    BasicBlock *ExitBB = BasicBlock::Create(Ctx, "exit", Func);

    IRBuilder<> Builder(EntryBB);

    FunctionCallee GetenvFunc = M.getOrInsertFunction(
        "getenv",
        FunctionType::get(CharPtrTy, {CharPtrTy}, false)
    );
    FunctionCallee PropGetFunc = M.getOrInsertFunction(
        "__system_property_get",
        FunctionType::get(Int32Ty, {CharPtrTy, CharPtrTy}, false)
    );
    FunctionCallee PopenFunc = M.getOrInsertFunction(
        "popen", FunctionType::get(CharPtrTy, {CharPtrTy, CharPtrTy}, false));
    FunctionCallee PcloseFunc = M.getOrInsertFunction(
        "pclose", FunctionType::get(Int32Ty, {CharPtrTy}, false));
    FunctionCallee FgetsFunc = M.getOrInsertFunction(
        "fgets", FunctionType::get(CharPtrTy, {CharPtrTy, Int32Ty, CharPtrTy}, false));
    FunctionCallee AtoiFunc = M.getOrInsertFunction(
        "atoi", FunctionType::get(Int32Ty, {CharPtrTy}, false));

    auto makeString = [&](const char *str) -> Constant* {
        return DetectUtils::createGlobalString(M, str, ".proxy.str");
    };

    Constant *HttpProxyEnv = makeString("http_proxy");
    Constant *HttpProxyEnvUpper = makeString("HTTP_PROXY");
    Constant *HttpsProxyEnv = makeString("https_proxy");
    Constant *HttpsProxyEnvUpper = makeString("HTTPS_PROXY");
    Constant *AllProxyEnv = makeString("all_proxy");
    // Android 系统代理属性
    Constant *Prop1Name = makeString("http.proxy");
    Constant *Prop2Name = makeString("global.http_proxy");
    Constant *Prop3Name = makeString("global_http_proxy_host");
    Constant *Prop4Name = makeString("global_http_proxy_port");
    Constant *SettingsCmd = makeString("settings get global http_proxy 2>/dev/null");
    Constant *ReadMode = makeString("r");
    Constant *ColonStr = makeString(":");

    Type *Buf92Ty = ArrayType::get(Int8Ty, 92);
    Value *Buf = Builder.CreateAlloca(Buf92Ty, nullptr, "propbuf");
    Value *BufPtr = Builder.CreateBitCast(Buf, CharPtrTy);

    // ===== 1. 环境变量 http_proxy =====
    Value *HttpProxy = Builder.CreateCall(GetenvFunc, {HttpProxyEnv});
    Value *HttpProxyNotNull = Builder.CreateICmpNE(HttpProxy, ConstantPointerNull::get(CharPtrTy));
    Builder.CreateCondBr(HttpProxyNotNull, FoundProxyBB, CheckHttpProxyBB);

    // ===== 2. HTTP_PROXY =====
    Builder.SetInsertPoint(CheckHttpProxyBB);
    Value *HttpProxyUpper = Builder.CreateCall(GetenvFunc, {HttpProxyEnvUpper});
    Value *HttpProxyUpperNotNull = Builder.CreateICmpNE(HttpProxyUpper, ConstantPointerNull::get(CharPtrTy));
    Builder.CreateCondBr(HttpProxyUpperNotNull, FoundProxyBB, CheckHttpsProxyBB);

    // ===== 3. https_proxy / HTTPS_PROXY =====
    Builder.SetInsertPoint(CheckHttpsProxyBB);
    Value *HttpsProxy = Builder.CreateCall(GetenvFunc, {HttpsProxyEnv});
    Value *HttpsProxyNotNull = Builder.CreateICmpNE(HttpsProxy, ConstantPointerNull::get(CharPtrTy));
    Builder.CreateCondBr(HttpsProxyNotNull, FoundProxyBB, CheckAllProxyBB);

    Builder.SetInsertPoint(CheckAllProxyBB);
    Value *HttpsProxyUpper = Builder.CreateCall(GetenvFunc, {HttpsProxyEnvUpper});
    Value *HttpsProxyUpperNotNull = Builder.CreateICmpNE(HttpsProxyUpper, ConstantPointerNull::get(CharPtrTy));
    Builder.CreateCondBr(HttpsProxyUpperNotNull, FoundProxyBB, CheckProp1BB);

    // ===== 4. all_proxy =====
    Builder.SetInsertPoint(CheckProp1BB);
    Value *AllProxy = Builder.CreateCall(GetenvFunc, {AllProxyEnv});
    Value *AllProxyNotNull = Builder.CreateICmpNE(AllProxy, ConstantPointerNull::get(CharPtrTy));
    Builder.CreateCondBr(AllProxyNotNull, FoundProxyBB, CheckProp2BB);

    // ===== 5. 系统属性 http.proxy =====
    Builder.SetInsertPoint(CheckProp2BB);
    Value *Len1 = Builder.CreateCall(PropGetFunc, {Prop1Name, BufPtr});
    Value *Len1Positive = Builder.CreateICmpSGT(Len1, ConstantInt::get(Int32Ty, 0));
    Builder.CreateCondBr(Len1Positive, FoundProxyBB, CheckProp3BB);

    // ===== 6. 系统属性 global.http_proxy =====
    Builder.SetInsertPoint(CheckProp3BB);
    Value *Len2 = Builder.CreateCall(PropGetFunc, {Prop2Name, BufPtr});
    Value *Len2Positive = Builder.CreateICmpSGT(Len2, ConstantInt::get(Int32Ty, 0));
    Builder.CreateCondBr(Len2Positive, FoundProxyBB, CheckProp4BB);

    // ===== 7. 系统属性 global_http_proxy_host =====
    Builder.SetInsertPoint(CheckProp4BB);
    Value *Len3 = Builder.CreateCall(PropGetFunc, {Prop3Name, BufPtr});
    Value *Len3Positive = Builder.CreateICmpSGT(Len3, ConstantInt::get(Int32Ty, 0));
    Builder.CreateCondBr(Len3Positive, FoundProxyBB, CheckSettingsBB);

    // ===== 8. 兜底: popen("settings get global http_proxy") =====
    Builder.SetInsertPoint(CheckSettingsBB);
    Value *Pipe = Builder.CreateCall(PopenFunc, {SettingsCmd, ReadMode});
    Value *PipeNotNull = Builder.CreateICmpNE(Pipe, ConstantPointerNull::get(CharPtrTy));
    Builder.CreateCondBr(PipeNotNull, ReadSettingsBB, ExitBB);

    Builder.SetInsertPoint(ReadSettingsBB);
    Value *Line = Builder.CreateCall(FgetsFunc, {BufPtr, ConstantInt::get(Int32Ty, 92), Pipe});
    Builder.CreateCall(PcloseFunc, {Pipe});
    Value *LineNotNull = Builder.CreateICmpNE(Line, ConstantPointerNull::get(CharPtrTy));
    Builder.CreateCondBr(LineNotNull, ParseValBB, ExitBB);

    Builder.SetInsertPoint(ParseValBB);
    // 返回值含 ":" 表示有 host:port 形式的代理设置（空设置只有换行）
    FunctionCallee StrstrFunc = M.getOrInsertFunction(
        "strstr", FunctionType::get(CharPtrTy, {CharPtrTy, CharPtrTy}, false));
    Value *HasColon = Builder.CreateCall(StrstrFunc, {BufPtr, ColonStr});
    Value *HasColonNotNull = Builder.CreateICmpNE(HasColon, ConstantPointerNull::get(CharPtrTy));
    Builder.CreateCondBr(HasColonNotNull, FoundProxyBB, ExitBB);

    Builder.SetInsertPoint(FoundProxyBB);
    Builder.CreateCall(reportFunc);
    Builder.CreateBr(ExitBB);

    Builder.SetInsertPoint(ExitBB);
    Builder.CreateRetVoid();

    return Func;
}
bool ProxyDetect::runOnModule(Module &M) {
    if (isIRObfuscationDebugEnabled()) {
        errs() << "[DEBUG] ProxyDetect: Injecting proxy detection\n";
    }
    Function *MainFunc = M.getFunction("main");
    if (!MainFunc || MainFunc->isDeclaration() || MainFunc->empty()) {
        return false;
    }
    // 使用公共模块创建报告函数
    Function *ReportFunc = DetectUtils::createReportAndKillFunc(M, "Proxy/iptables");
    
    // 创建检测函数
    Function *CheckFunc = createProxyCheckFunc(M, ReportFunc);
    
    // 配置选项
    DetectOptions opts = DetectOptions::create(false);
    
    // 注入到main函数
    return DetectUtils::injectToMain(M, CheckFunc, opts);
}

ModulePass *llvm::createProxyDetectPass() {
    return new ProxyDetect();
}
INITIALIZE_PASS_BEGIN(ProxyDetect, "proxydetect", "Inject proxy detection at program start", false, false)
INITIALIZE_PASS_END(ProxyDetect, "proxydetect", "Inject proxy detection at program start", false, false)