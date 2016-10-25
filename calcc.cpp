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

static int64_t read_int_const(int64_t so_far){
    int c = '0';
    while(c >= '0' && c <= '9'){
        so_far = 10*so_far + c-'0';
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
        int64_t num = read_int_const(c-'0');
        return {Token::intconst,num};
    } else if ('-' == c){
        c = getchar();
        if (c >= '0' && c <= '9'){
            int64_t num = read_int_const(c - '0');
            Token ret = {Token::intconst, num*-1};
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
        int64_t num = read_int_const(0);
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
        return {Token::boolconst,0};
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
static Value* parse_expr(BasicBlock *bb, Function * f);

static Value* parse_arith(BasicBlock *bb, Function *f, Token t){
    Value *l = parse_expr(bb, f);
    Value *r = parse_expr(bb, f);
    Token rpar = lex_one();
    if (Token::rparen != rpar.k){
        error("expected right paren, got something else.");
    }
    Value *result;
    if (Token::add == t.k){
        result = BinaryOperator::CreateAdd(l, r, "arithresult", bb);
    } else if (Token::sub == t.k){
        result = BinaryOperator::CreateSub(l, r, "arithresult", bb);
    } else if (Token::mul == t.k){
        result = BinaryOperator::CreateMul(l, r, "arithresult", bb);
    } else if (Token::div == t.k){
        //error("not yet implemented");
        result = BinaryOperator::CreateSDiv(l, r, "arithresult", bb);
    } else if (Token::mod == t.k){
        error("mod not yet implemented");
        //result = BinaryOperator::CreateMod(l, r, "arithresult", bb);
    }
    return result;
}

static Value* parse_lparen(BasicBlock *bb, Function * f){
    Token t = lex_one();
    if (Token::add == t.k){
        return parse_arith(bb, f, t);
    } else if (Token::sub == t.k){
        return parse_arith(bb, f, t);
    } else if (Token::mul == t.k){
        return parse_arith(bb, f, t);
    } else if (Token::div == t.k){
        return parse_arith(bb, f, t);
    } else if (Token::mod == t.k){
        return parse_arith(bb, f, t);
    } else if (Token::ift == t.k){
        error("if not yet implemented");
        //parse_if();
    }
}

static Value* parse_expr(BasicBlock *bb, Function * f){
    Token t = lex_one();
    if (Token::lparen == t.k){
        return parse_lparen(bb, f);
    } else if (Token::programarg == t.k){
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
  Value *v = parse_expr(BB, F);
  ReturnInst::Create(C, v, BB);
  /////////////////////////// end my code

  //Value *RetVal = ConstantInt::get(C, APInt(64, 0));
  //Builder.CreateRet(RetVal);
  assert(!verifyModule(*M, &outs()));
  M->dump();
  return 0;
}

int main(void) { return compile(); }
