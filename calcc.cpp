#include "llvm/ADT/APInt.h"
#include "llvm/IR/ConstantRange.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/NoFolder.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>
#include <iostream>

using namespace llvm;
using namespace std;

static LLVMContext C;
static IRBuilder<NoFolder> Builder(C);
static std::unique_ptr<Module> M = llvm::make_unique<Module>("calc", C);
static std::vector<Value*> mvars = vector<Value*>();

/////////////////////// begin my code
#include <stdio.h>
#include <stdint.h>

struct Token {
    enum Tokenkind {lparen, rparen, intconst, add, sub, mul, div, mod, ift,
                    gt, gte, lt, lte, eq, neq, boolconst, programarg, eof,
                    set, seq, whilet, mvar};
    Tokenkind k;
    int64_t val;
    int64_t line;
    int64_t col;
    int64_t pos;
};

// position and line both start at 1, but emacs and racket both have column start at 0.
// since I increment them before anything, they need to start 1 lower.
static int64_t curpos = 0;
static int64_t curline = 0;
static int64_t curcol = -1;
static int64_t last_line_col = -999;

static int cget(){
    int c = getchar();
    ++curpos;
    ++curcol;
    if ('\n' == c){
        ++curline;
        last_line_col = curcol;
        curcol = -1;
    }
    return c;
}
static int cunget(int c){
    --curpos;
    if ('\n' == c){
        --curline;
        curcol = last_line_col - 1;
    }
    return ungetc(c,stdin);
}

static int error(const char* msg){
    puts(msg);
    exit(1);
}

/////////////////////////// lex /////////////////////////////
// TODO - I can use `auto mb = memorybuffer::getstdin()` (with some uppercase letters)
//        to get a big buffer of the characters, rather than using getc and ungetc.

static void ignore_to_newline(){
    char c = cget();
    for(; c != '\n'; c = cget());
    cunget(c);
}

static int64_t read_int_const(int64_t so_far, bool negativep){
    int c = cget();
    int64_t last;
    while(c >= '0' && c <= '9'){
        last = so_far;
        so_far *= 10;
        if(negativep){
            so_far -= c-'0';
            if(so_far > last){
                error("integer overflow negative to positive");
            }
        } else {
            so_far += c-'0';
            if(so_far < last){
                error("integer overflow positive to negative");
            }
        }
        c = cget();
    }
    cunget(c);
    return so_far;
}

static Token lex_one(){
    static int first_line = 1;
    // a very very bad lexer
    int c = cget();
    //printf("in lexer with %c\n");
    if (first_line && '#' == c){
        first_line = 0;
        ignore_to_newline();
        return lex_one();
    } else if ('\n' == c){
        first_line = 0;
        c = cget();
        if ('#' == c){
            ignore_to_newline();
        } else {
            cunget(c);
        }
        // Tail call to self.  Will it be optimized into a goto?
        return lex_one();
    } else if (' ' == c || '\t' == c){
        return lex_one();
    } else if ('(' == c){
        return {Token::lparen,0,curline,curcol,curpos};
    } else if (')' == c){
        return {Token::rparen,0,curline,curcol,curpos};
    } else if (c >= '0' && c <= '9'){
        int64_t num = read_int_const(c-'0',false);
        return {Token::intconst,num,curline,curcol,curpos};
    } else if ('-' == c){
        c = cget();
        if (c >= '0' && c <= '9'){
            int64_t num = read_int_const(-(c - '0'),true);
            Token ret = {Token::intconst, num,curline,curcol,curpos};
            return ret;
        } else {
            cunget(c);
            return {Token::sub,0,curline,curcol,curpos};
        }
    } else if ('+' == c){
        return {Token::add,0,curline,curcol,curpos};
    } else if ('*' == c){
        return {Token::mul,0,curline,curcol,curpos};
    } else if ('/' == c){
        return {Token::div,0,curline,curcol,curpos};
    } else if ('%' == c){
        return {Token::mod,0,curline,curcol,curpos};
    } else if ('>' == c){
        c = cget();
        if ('=' == c){
            return {Token::gte,0,curline,curcol,curpos};
        } else {
            cunget(c);
            return {Token::gt,0,curline,curcol,curpos};
        }
    } else if ('<' == c){
        c = cget();
        if ('=' == c){
            return {Token::lte,0,curline,curcol,curpos};
        } else {
            cunget(c);
            return {Token::lt,0,curline,curcol,curpos};
        }
    } else if ('!' == c){
        c = cget();
        if ('=' == c){
            return {Token::neq,0,curline,curcol,curpos};
        } else {
            error("expected = character after !");
        }
    } else if ('=' == c){
        c = cget();
        if ('=' == c){
            return {Token::eq,0,curline,curcol,curpos};
        } else {
            error("expected = character after =");
        }
    } else if ('a' == c){
        c = cget();
        int64_t num = c - '0';
        if (num < 0 || num > 5){
            error("argument index out of range");
        }
        return {Token::programarg,num,curline,curcol,curpos};
    } else if ('m' == c){
        c = cget();
        int64_t num = c - '0';
        if (num < 0 || num > 9){
            error("variable index out of range");
        }
        return {Token::mvar,num,curline,curcol,curpos};
    } else if ('f' == c){
        // for now, assume it's false
        (cget() == 'a' && cget() == 'l' && cget() == 's' && cget() == 'e')
            || error("error lexing false");
        return {Token::boolconst,0,curline,curcol,curpos};
    } else if ('t' == c){
        // for now, assume it's true
        (cget() == 'r' && cget() == 'u' && cget() == 'e')
            || error("error lexing true");
        return {Token::boolconst,1,curline,curcol,curpos};
    } else if ('i' == c){
        // for now, assume it's if
        (cget() == 'f') || error("error lexing true");
        return {Token::ift,0,curline,curcol,curpos};
    } else if ('s' == c){
        (cget() == 'e') || error("error lexing seq or set");
        c = cget();
        if ('q' == c){
            return {Token::seq,0,curline,curcol,curpos};
        } else if ('t' == c){
            return {Token::set,0,curline,curcol,curpos};
        } else {
            error("error lexing seq or set");
        }
    } else if ('w' == c){
        // for now, assume it's true
        (cget() == 'h' && cget() == 'i' && cget() == 'l' && cget() == 'e')
            || error("error lexing true");
        return {Token::whilet,0,curline,curcol,curpos};
    } else if (EOF == c){
        return {Token::eof,0,curline,curcol,curpos};
    } else {
        error("unknown error lexing");
    }
}



/////////////////////////// parse /////////////////////////////
static Value* parse_expr();

static Value* parse_arith(Token t){
    Value *l = parse_expr();
    Value *r = parse_expr();
    Token rpar = lex_one();
    if (Token::rparen != rpar.k){
        error("expected right paren, got something else.");
    }
    Value *result = nullptr;
    if (Token::add == t.k){
        result = Builder.CreateAdd(l, r, "+");
    } else if (Token::sub == t.k){
        result = Builder.CreateSub(l, r, "-");
    } else if (Token::mul == t.k){
        result = Builder.CreateMul(l, r, "*");
    } else if (Token::div == t.k){
        result = Builder.CreateSDiv(l, r, "/");
    } else if (Token::mod == t.k){
        result = Builder.CreateSRem(l, r, "%");
    } else {
        error("expected arithmetic operator");
    }
    return result;
}

static Value* parse_compare(Token t){
    Value *l = parse_expr();
    Value *r = parse_expr();
    Token rpar = lex_one();
    if (Token::rparen != rpar.k){
        error("expected right paren, got something else.");
    }

    Value *ret;
    if (Token::eq == t.k){
        ret = Builder.CreateICmpEQ(l, r, "==");
    } else if (Token::neq == t.k){
        ret = Builder.CreateICmpNE(l, r, "!=");
    } else if (Token::lt == t.k){
        ret = Builder.CreateICmpSLT(l, r, "<");
    } else if (Token::gt == t.k){
        ret = Builder.CreateICmpSGT(l, r, ">");
    } else if (Token::lte == t.k){
        ret = Builder.CreateICmpSLE(l, r, "<=");
    } else if (Token::gte == t.k){
        ret = Builder.CreateICmpSGE(l, r, ">=");
    } else {
        error("expected equality operator");
    }
    return ret;
}

static Value* parse_bool_expr(){
    Token t = lex_one();
    if (Token::boolconst == t.k){
        Value *c = ConstantInt::get(Type::getInt1Ty(C), t.val);
        return c;
    } else if (Token::lparen == t.k){
        t = lex_one();
        return parse_compare(t);
    }
}

static Value* parse_ift(){

    Value *test = parse_bool_expr();

    BasicBlock *startbb = Builder.GetInsertBlock();
    Function *f = startbb->getParent();
    BasicBlock *tblock = BasicBlock::Create(C, "true", f);
    BasicBlock *fblock = BasicBlock::Create(C, "false");
    BasicBlock *mergebb = BasicBlock::Create(C, "merge");

    Builder.CreateCondBr(test, tblock, fblock);

    Builder.SetInsertPoint(tblock);
    Value *iftrue = parse_expr();
    Builder.CreateBr(mergebb);
    BasicBlock *fromtrue = Builder.GetInsertBlock();

    f->getBasicBlockList().push_back(fblock);
    Builder.SetInsertPoint(fblock);
    Value *iffalse = parse_expr();
    Builder.CreateBr(mergebb);
    BasicBlock *fromfalse = Builder.GetInsertBlock();


    Builder.SetInsertPoint(mergebb);
    f->getBasicBlockList().push_back(mergebb);
    PHINode *pn = Builder.CreatePHI(Type::getInt64Ty(C), 2, "ifret");
    pn->addIncoming(iftrue, fromtrue);
    pn->addIncoming(iffalse, fromfalse);

    Token rpar = lex_one();
    if (Token::rparen != rpar.k){
        error("expected right paren, got something else.");
    }

    return pn;
}

static Value* parse_whilet(){

    BasicBlock *origbb = Builder.GetInsertBlock();
    Function *f = origbb->getParent();
    BasicBlock *testbb = BasicBlock::Create(C, "test");
    BasicBlock *bodybb = BasicBlock::Create(C, "body");
    BasicBlock *exitbb = BasicBlock::Create(C, "exit");

    Builder.CreateBr(testbb);
    f->getBasicBlockList().push_back(testbb);
    Builder.SetInsertPoint(testbb);
    PHINode * exitv = Builder.CreatePHI(Type::getInt64Ty(C), 2, "loop value");
    exitv->addIncoming(ConstantInt::get(Type::getInt64Ty(C), 0), origbb);
    Value *test = parse_bool_expr();
    BasicBlock *fromtestbb = Builder.GetInsertBlock();
    Builder.CreateCondBr(test, bodybb, exitbb);

    f->getBasicBlockList().push_back(bodybb);
    Builder.SetInsertPoint(bodybb);
    Value *bodyexpr = parse_expr();
    Builder.CreateBr(testbb);
    BasicBlock *frombodybb = Builder.GetInsertBlock();
    exitv->addIncoming(bodyexpr, frombodybb);

    f->getBasicBlockList().push_back(exitbb);
    Builder.SetInsertPoint(exitbb);
    // Add a phi node with only one incoming edge, because I'm not sure
    // of any other way to just tell it to reference a previous value.
    PHINode * output = Builder.CreatePHI(Type::getInt64Ty(C), 1, "return");
    output->addIncoming(exitv, fromtestbb);

    Token rpar = lex_one();
    if (Token::rparen != rpar.k){
        error("expected right paren, got something else.");
    }

    return output;
}

static Value* parse_expr(){
    Token t = lex_one();
    if (Token::lparen == t.k){
        t = lex_one();
        if(Token::ift == t.k){
            return parse_ift();
        } else if (Token::seq == t.k){
            Value *l = parse_expr();
            Value *r = parse_expr();
            Token rparen = lex_one();
            if (Token::rparen != rparen.k){
                error("expected right paren, got something else.");
            }
            return r;
        } else if (Token::set == t.k){
            Value *v = parse_expr();
            // just lex the mvar -- parsing it will emit a load instruction.
            Token mvar = lex_one();
            Token rpar = lex_one();
            if (Token::rparen != rpar.k){
                error("expected right paren, got something else.");
            } else if (Token::mvar != mvar.k){
                error("expected variable name in set expression, got something else");
            }
            Value *store = Builder.CreateStore(v, mvars[mvar.val]);
            return v;
        } else if (Token::whilet == t.k){
            return parse_whilet();
        } else {
            return parse_arith(t);
        }
    } else if (Token::programarg == t.k){
        Function *f = Builder.GetInsertBlock()->getParent();
        auto arg_iter = f->arg_begin();
        // Oh, man, I don't know how to use C++ iterators...
        for(int i = 0; i < t.val; ++i){
            ++arg_iter;
        }
        // &* is what the fibonacci example does... maybe * is overloaded for iterators?
        Argument *a = &*arg_iter;
        return a;
    } else if (Token::mvar == t.k){
        if (t.val > 9 || t.val < 0){
            error("variable name out of bounds");
        }
        Value *load = Builder.CreateLoad(mvars[t.val]);
        return load;
    } else if (Token::intconst == t.k){
        Value *c = ConstantInt::get(Type::getInt64Ty(C), t.val);
        return c;
    } else {
        error("parse error: expected expression, got something else");
    }
}


/////////////////////// end my code

static int compile() {
  M->setTargetTriple(llvm::sys::getProcessTriple());
  std::vector<Type *> SixInts(6, Type::getInt64Ty(C));
  FunctionType *FT = FunctionType::get(Type::getInt64Ty(C), SixInts, false);
  Function *F = Function::Create(FT, Function::ExternalLinkage, "f", &*M);
  BasicBlock *BB = BasicBlock::Create(C, "entry", F);
  Builder.SetInsertPoint(BB);

  /////////////////////////// begin my code

  // set up memory for 10 mutable variables
  Value *zeroconst = ConstantInt::get(Type::getInt64Ty(C), 0);
  for(int i=0; i<10; ++i){
      Value *loc = Builder.CreateAlloca(Type::getInt64Ty(C));
      Builder.CreateStore(zeroconst, loc);
      mvars.push_back(loc);
  }

  Value *v = parse_expr();
  ReturnInst::Create(C, v, Builder.GetInsertBlock());
  Token t = lex_one();
  if (Token::eof != t.k){
      error("Expected EOF, got something else.");
  }
  /////////////////////////// end my code

  //Value *RetVal = ConstantInt::get(C, APInt(64, 0));
  //Builder.CreateRet(RetVal);
  M->dump();
  assert(!verifyModule(*M, &outs()));
  return 0;
}

int main(void) { return compile(); }
