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

/////////////////////// begin my code
#include <stdio.h>
#include <stdint.h>

struct Token {
    enum Tokenkind {lparen, rparen, intconst, add, sub, mul, div, mod, ift,
                    gt, gte, lt, lte, eq, neq, boolconst, programarg, eof};
    Tokenkind k;
    int64_t val;
};

static int ungetchar(int c){
    return ungetc(c,stdin);
}

static int error(char* msg){
    puts(msg);
    exit(1);
}

/////////////////////////// lex /////////////////////////////

static void ignore_to_newline(){
    char c = getchar();
    for(; c != '\n'; c = getchar());
    ungetchar(c);
}

static int64_t read_int_const(int64_t so_far, bool negativep){
    int c = getchar();
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
        c = getchar();
    }
    ungetchar(c);
    return so_far;
}

static Token lex_one(){
    static int first_line = 1;
    // a very very bad lexer
    int c = getchar();
    //printf("in lexer with %c\n");
    if (first_line && '#' == c){
        first_line = 0;
        ignore_to_newline();
        return lex_one();
    } else if ('\n' == c){
        first_line = 0;
        c = getchar();
        if ('#' == c){
            ignore_to_newline();
        } else {
            ungetchar(c);
        }
        // Tail call to self.  Will it be optimized into a goto?
        return lex_one();
    } else if (' ' == c || '\t' == c){
        return lex_one();
    } else if ('(' == c){
        return {Token::lparen,0};
    } else if (')' == c){
        return {Token::rparen,0};
    } else if (c >= '0' && c <= '9'){
        int64_t num = read_int_const(c-'0',false);
        return {Token::intconst,num};
    } else if ('-' == c){
        c = getchar();
        if (c >= '0' && c <= '9'){
            int64_t num = read_int_const(-(c - '0'),true);
            Token ret = {Token::intconst, num};
            return ret;
        } else {
            ungetchar(c);
            return {Token::sub,0};
        }
    } else if ('+' == c){
        return {Token::add,0};
    } else if ('*' == c){
        return {Token::mul,0};
    } else if ('/' == c){
        return {Token::div,0};
    } else if ('%' == c){
        return {Token::mod,0};
    } else if ('>' == c){
        c = getchar();
        if ('=' == c){
            return {Token::gte,0};
        } else {
            ungetchar(c);
            return {Token::gt,0};
        }
    } else if ('<' == c){
        c = getchar();
        if ('=' == c){
            return {Token::lte,0};
        } else {
            ungetchar(c);
            return {Token::lt,0};
        }
    } else if ('!' == c){
        c = getchar();
        if ('=' == c){
            return {Token::neq,0};
        } else {
            error("expected = character after !");
        }
    } else if ('=' == c){
        c = getchar();
        if ('=' == c){
            return {Token::eq,0};
        } else {
            error("expected = character after =");
        }
    } else if ('a' == c){
        int64_t num = read_int_const(0,false);
        return {Token::programarg,num};
    } else if ('f' == c){
        // for now, assume it's false
        (getchar() == 'a' && getchar() == 'l' && getchar() == 's' && getchar() == 'e')
            || error("error lexing false");
        return {Token::boolconst,0};
    } else if ('t' == c){
        // for now, assume it's true
        (getchar() == 'r' && getchar() == 'u' && getchar() == 'e')
            || error("error lexing true");
        return {Token::boolconst,1};
    } else if ('i' == c){
        // for now, assume it's if
        (getchar() == 'f') || error("error lexing true");
        return {Token::ift,0};
    } else if (EOF == c){
        return {Token::eof,0};
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
    Value *result;
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

static Value* parse_expr(){
    Token t = lex_one();
    if (Token::lparen == t.k){
        t = lex_one();
        if(Token::ift == t.k){
            return parse_ift();
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
  Value *v = parse_expr();
  ReturnInst::Create(C, v, Builder.GetInsertBlock());
  Token t = lex_one();
  if (Token::eof != t.k){
      error("Expected EOF, got something else.");
  }
  /////////////////////////// end my code

  //Value *RetVal = ConstantInt::get(C, APInt(64, 0));
  //Builder.CreateRet(RetVal);
  assert(!verifyModule(*M, &outs()));
  M->dump();
  return 0;
}

int main(void) { return compile(); }
