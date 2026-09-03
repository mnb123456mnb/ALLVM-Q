//===- VpnDetect.cpp - VPN检测注入Pass ------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
#include "llvm/Transforms/Obfuscation/VpnDetect.h"
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
#define DEBUG_TYPE "vpndetect"
using namespace llvm;
namespace {

struct VpnDetect : public ModulePass {
    static char ID;
    VpnDetect() : ModulePass(ID) {
        initializeVpnDetectPass(*PassRegistry::getPassRegistry());
    }
    StringRef getPassName() const override {
        return {"VpnDetect"};
    }
    bool runOnModule(Module &M) override;

    Function* createVpnCheckFunc(Module &M, Function *reportFunc);
};
}
char VpnDetect::ID = 0;

// VPN 判定（防误报版）：
//   方法1(主): ioctl(SIOCGIFFLAGS) 逐个精确探测 tun0..tun9 —— Android VpnService
//              客户端侧网卡固定为 tunN，精确名字匹配天然排除内核固定接口 tunl0
//              (ipip 隧道，所有 Android 都有；旧版裸 strstr("tun") 的误报源头)
//   方法2(兜底): /proc/net/dev 行内匹配 "tun<数字>:" —— tun 后必须紧跟数字且
//              数字区以 ':' 结束（接口名分隔符），tunl0/gre0 等不会命中
Function* VpnDetect::createVpnCheckFunc(Module &M, Function *reportFunc) {
    LLVMContext &Ctx = M.getContext();

    Type *VoidTy = Type::getVoidTy(Ctx);
    Type *Int8Ty = Type::getInt8Ty(Ctx);
    Type *Int32Ty = Type::getInt32Ty(Ctx);
    Type *Int64Ty = Type::getInt64Ty(Ctx);
    PointerType *CharPtrTy = PointerType::get(Ctx, 0);

    FunctionType *FuncTy = FunctionType::get(VoidTy, {}, false);
    Function *Func = Function::Create(
        FuncTy,
        GlobalValue::InternalLinkage,
        M.getDataLayout().getProgramAddressSpace(),
        "vpn_check",
        &M
    );

    Func->addFnAttr(Attribute::NoInline);

    // 方法1 的基本块
    BasicBlock *EntryBB = BasicBlock::Create(Ctx, "entry", Func);
    BasicBlock *SockOkBB = BasicBlock::Create(Ctx, "sock_ok", Func);
    BasicBlock *IoctlLoopBB = BasicBlock::Create(Ctx, "ioctl_loop", Func);
    BasicBlock *IoctlBodyBB = BasicBlock::Create(Ctx, "ioctl_body", Func);
    BasicBlock *IoctlHitBB = BasicBlock::Create(Ctx, "ioctl_hit", Func);
    BasicBlock *IoctlNextBB = BasicBlock::Create(Ctx, "ioctl_next", Func);
    BasicBlock *IoctlDoneBB = BasicBlock::Create(Ctx, "ioctl_done", Func);
    // 方法2(兜底) 的基本块
    BasicBlock *FbOpenBB = BasicBlock::Create(Ctx, "fb_open", Func);
    BasicBlock *FbOpenOkBB = BasicBlock::Create(Ctx, "fb_open_ok", Func);
    BasicBlock *FbOpenFailBB = BasicBlock::Create(Ctx, "fb_open_fail", Func);
    BasicBlock *FbLoopBB = BasicBlock::Create(Ctx, "fb_loop", Func);
    BasicBlock *FbCheckBB = BasicBlock::Create(Ctx, "fb_check", Func);
    BasicBlock *FbTunDigitBB = BasicBlock::Create(Ctx, "fb_tun_digit", Func);
    // 公共
    BasicBlock *FoundVpnBB = BasicBlock::Create(Ctx, "found_vpn", Func);
    BasicBlock *ExitBB = BasicBlock::Create(Ctx, "exit", Func);

    IRBuilder<> Builder(EntryBB);

    FunctionCallee SocketFunc = M.getOrInsertFunction(
        "socket",
        FunctionType::get(Int32Ty, {Int32Ty, Int32Ty, Int32Ty}, false)
    );

    FunctionCallee IoctlFunc = M.getOrInsertFunction(
        "ioctl",
        // 与 bionic <sys/ioctl.h> 声明一致: int ioctl(int, unsigned long, ...)
        // 避免 target 模块自身调用过 ioctl 时签名冲突
        FunctionType::get(Int32Ty, {Int32Ty, Int64Ty, CharPtrTy}, true)
    );

    FunctionCallee SnprintfFunc = M.getOrInsertFunction(
        "snprintf",
        FunctionType::get(Int32Ty, {CharPtrTy, Int64Ty, CharPtrTy}, true)
    );

    FunctionCallee MemsetFunc = M.getOrInsertFunction(
        "memset",
        FunctionType::get(CharPtrTy, {CharPtrTy, Int32Ty, Int64Ty}, false)
    );

    FunctionCallee CloseFunc = M.getOrInsertFunction(
        "close",
        FunctionType::get(Int32Ty, {Int32Ty}, false)
    );

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

    FunctionCallee StrspnFunc = M.getOrInsertFunction(
        "strspn",
        FunctionType::get(Int64Ty, {CharPtrTy, CharPtrTy}, false)
    );

    auto makeString = [&](const char *str) -> Constant* {
        return DetectUtils::createGlobalString(M, str, ".vpn.str");
    };

    Constant *IfNameFmt = makeString("tun%d");
    Constant *DigitCharset = makeString("0123456789");
    Constant *NetDevPath = makeString("/proc/net/dev");
    Constant *ReadMode = makeString("r");
    Constant *TunNeedle = makeString("tun");

    // ===== 方法1: ioctl 探测 tun0..tun9 =====
    // sock = socket(AF_INET=2, SOCK_DGRAM=2, 0)
    Value *Sock = Builder.CreateCall(SocketFunc, {
        ConstantInt::get(Int32Ty, 2),
        ConstantInt::get(Int32Ty, 2),
        ConstantInt::get(Int32Ty, 0)
    });
    Value *SockOk = Builder.CreateICmpSGE(Sock, ConstantInt::get(Int32Ty, 0));
    Builder.CreateCondBr(SockOk, SockOkBB, FbOpenBB);

    // SockOk: 准备名字缓冲与循环计数
    Builder.SetInsertPoint(SockOkBB);
    Type *NameBufTy = ArrayType::get(Int8Ty, 64);
    Value *NameBuf = Builder.CreateAlloca(NameBufTy, nullptr, "namebuf");
    Value *NameBufPtr = Builder.CreateBitCast(NameBuf, CharPtrTy);
    Builder.CreateCall(MemsetFunc, {
        NameBufPtr,
        ConstantInt::get(Int32Ty, 0),
        ConstantInt::get(Int64Ty, 64)
    });
    Value *Counter = Builder.CreateAlloca(Int32Ty, nullptr, "iface_idx");
    Builder.CreateStore(ConstantInt::get(Int32Ty, 0), Counter);
    Builder.CreateBr(IoctlLoopBB);

    // IoctlLoop: for i in 0..9
    Builder.SetInsertPoint(IoctlLoopBB);
    Value *Idx = Builder.CreateLoad(Int32Ty, Counter);
    Value *Cont = Builder.CreateICmpSLT(Idx, ConstantInt::get(Int32Ty, 10));
    Builder.CreateCondBr(Cont, IoctlBodyBB, IoctlDoneBB);

    // IoctlBody: snprintf(name, 16, "tun%d", i); ioctl(sock, SIOCGIFFLAGS, name)
    Builder.SetInsertPoint(IoctlBodyBB);
    Builder.CreateCall(SnprintfFunc, {
        NameBufPtr,
        ConstantInt::get(Int64Ty, 16),
        IfNameFmt,
        Idx
    });
    // SIOCGIFFLAGS = 0x8913
    Value *IoctlRet = Builder.CreateCall(IoctlFunc, {
        Sock,
        ConstantInt::get(Int64Ty, 0x8913),
        NameBufPtr
    });
    Value *IfExists = Builder.CreateICmpEQ(IoctlRet, ConstantInt::get(Int32Ty, 0));
    Builder.CreateCondBr(IfExists, IoctlHitBB, IoctlNextBB);

    // IoctlHit: 接口存在 => VPN 在线
    Builder.SetInsertPoint(IoctlHitBB);
    Builder.CreateCall(CloseFunc, {Sock});
    Builder.CreateCall(reportFunc);
    Builder.CreateBr(ExitBB);

    // IoctlNext: ++i
    Builder.SetInsertPoint(IoctlNextBB);
    Value *IdxNext = Builder.CreateNSWAdd(Idx, ConstantInt::get(Int32Ty, 1));
    Builder.CreateStore(IdxNext, Counter);
    Builder.CreateBr(IoctlLoopBB);

    // IoctlDone: ioctl 全查完未命中，收尾后走兜底
    Builder.SetInsertPoint(IoctlDoneBB);
    Builder.CreateCall(CloseFunc, {Sock});
    Builder.CreateBr(FbOpenBB);

    // ===== 方法2(兜底): /proc/net/dev 匹配 "tun<数字>:" =====
    Builder.SetInsertPoint(FbOpenBB);
    Value *Fp = Builder.CreateCall(FopenFunc, {NetDevPath, ReadMode});
    Value *FpNotNull = Builder.CreateICmpNE(Fp, ConstantPointerNull::get(CharPtrTy));
    Builder.CreateCondBr(FpNotNull, FbOpenOkBB, FbOpenFailBB);

    Builder.SetInsertPoint(FbOpenFailBB);
    Builder.CreateBr(ExitBB);

    Builder.SetInsertPoint(FbOpenOkBB);

    Type *LineBufTy = ArrayType::get(Int8Ty, 512);
    Value *LineBuf = Builder.CreateAlloca(LineBufTy, nullptr, "linebuf");
    Value *LineBufPtr = Builder.CreateBitCast(LineBuf, CharPtrTy);

    Builder.CreateBr(FbLoopBB);

    Builder.SetInsertPoint(FbLoopBB);

    Value *Line = Builder.CreateCall(FgetsFunc, {LineBufPtr, ConstantInt::get(Int32Ty, 512), Fp});
    Value *LineNotNull = Builder.CreateICmpNE(Line, ConstantPointerNull::get(CharPtrTy));
    Builder.CreateCondBr(LineNotNull, FbCheckBB, ExitBB);

    Builder.SetInsertPoint(FbCheckBB);

    Value *FoundTun = Builder.CreateCall(StrstrFunc, {LineBufPtr, TunNeedle});
    Value *FoundTunNotNull = Builder.CreateICmpNE(FoundTun, ConstantPointerNull::get(CharPtrTy));
    Builder.CreateCondBr(FoundTunNotNull, FbTunDigitBB, FbLoopBB);

    Builder.SetInsertPoint(FbTunDigitBB);
    // FoundTun 指向 "tun..."，跳过 "tun" 三个字符到数字区
    Value *AfterTun = Builder.CreateConstInBoundsGEP1_64(Builder.getInt8Ty(), FoundTun, 3);
    // 统计连续数字个数: strspn(AfterTun, "0123456789")
    Value *DigitCount = Builder.CreateCall(StrspnFunc, {AfterTun, DigitCharset});
    Value *HasDigit = Builder.CreateICmpUGE(DigitCount, Builder.getInt64(1));
    // 数字区之后必须紧跟 ':' （接口名结束符），tun0/tun1/tun2... 全覆盖
    Value *ColonPos = Builder.CreateGEP(Builder.getInt8Ty(), AfterTun, DigitCount);
    Value *ColonChar = Builder.CreateLoad(Builder.getInt8Ty(), ColonPos);
    Value *IsColon = Builder.CreateICmpEQ(ColonChar, Builder.getInt8(58));
    Value *IsVpnIface = Builder.CreateAnd(HasDigit, IsColon);
    Builder.CreateCondBr(IsVpnIface, FoundVpnBB, FbLoopBB);

    Builder.SetInsertPoint(FoundVpnBB);
    Builder.CreateCall(FcloseFunc, {Fp});
    Builder.CreateCall(reportFunc);
    Builder.CreateBr(ExitBB);

    Builder.SetInsertPoint(ExitBB);
    Builder.CreateRetVoid();

    return Func;
}
bool VpnDetect::runOnModule(Module &M) {
    if (isIRObfuscationDebugEnabled()) {
        errs() << "[DEBUG] VpnDetect: Injecting VPN detection\n";
    }

    Function *MainFunc = M.getFunction("main");
    if (!MainFunc || MainFunc->isDeclaration() || MainFunc->empty()) {
        return false;
    }
    // 使用公共模块创建报告函数
    Function *ReportFunc = DetectUtils::createReportAndKillFunc(M, "VPN Connection");

    // 创建检测函数
    Function *CheckFunc = createVpnCheckFunc(M, ReportFunc);

    // 配置选项
    DetectOptions opts = DetectOptions::create(false);

    // 注入到main函数
    return DetectUtils::injectToMain(M, CheckFunc, opts);
}
ModulePass *llvm::createVpnDetectPass() {
    return new VpnDetect();
}
INITIALIZE_PASS_BEGIN(VpnDetect, "vpndetect", "Inject VPN detection at program start", false, false)
INITIALIZE_PASS_END(VpnDetect, "vpndetect", "Inject VPN detection at program start", false, false)