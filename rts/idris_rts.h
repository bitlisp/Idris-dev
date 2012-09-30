#ifndef _IDRISRTS_H
#define _IDRISRTS_H

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <stdarg.h>

// Closures

typedef enum {
    CON, INT, BIGINT, FLOAT, STRING, UNIT, PTR, FWD
} ClosureType;

typedef struct Closure *VAL;

typedef struct {
    int tag;
    int arity;
    VAL args[];
} con;

typedef struct Closure {
    ClosureType ty;
    union {
        con c;
        int i;
        double f;
        char* str;
        void* ptr;
    } info;
} Closure;

typedef struct {
    VAL* valstack;
    int* intstack;
    double* floatstack;
    VAL* valstack_top;
    VAL* valstack_base;
    int* intstack_ptr;
    double* floatstack_ptr;
    char* heap;
    char* oldheap;
    char* heap_next;
    char* heap_end;
    VAL* stack_max;
    size_t heap_size;
    size_t heap_growth;
    int allocations;
    int collections;
    VAL ret;
    VAL reg1;
} VM;

VM* init_vm(int stack_size, size_t heap_size);

// Functions all take a pointer to their VM, and previous stack base, 
// and return nothing.
typedef void(*func)(VM*, VAL*);

// Register access 

#define RVAL (vm->ret)
#define LOC(x) (*(vm->valstack_base + (x)))
#define TOP(x) (*(vm->valstack_top + (x)))
#define REG1 (vm->reg1)

// Retrieving values

#define GETSTR(x) (((VAL)(x))->info.str) 
#define GETPTR(x) (((VAL)(x))->info.ptr) 
#define GETFLOAT(x) (((VAL)(x))->info.f)

#define TAG(x) (ISINT(x) ? (-1) : ( (x)->ty == CON ? (x)->info.c.tag : (-1)) )

// Integers, floats and operators

typedef intptr_t i_int;

#define MKINT(x) ((void*)((x)<<1)+1)
#define GETINT(x) ((i_int)(x)>>1)
#define ISINT(x) ((((i_int)x)&1) == 1)

#define INTOP(op,x,y) MKINT((i_int)((((i_int)x)>>1) op (((i_int)y)>>1)))
#define FLOATOP(op,x,y) MKFLOAT(((GETFLOAT(x)) op (GETFLOAT(y))))
#define FLOATBOP(op,x,y) MKINT((i_int)(((GETFLOAT(x)) op (GETFLOAT(y)))))
#define ADD(x,y) (void*)(((i_int)x)+(((i_int)y)-1))
#define MULT(x,y) (MKINT((((i_int)x)>>1) * (((i_int)y)>>1)))

// Stack management

#define INITFRAME VAL* myoldbase
#define REBASE vm->valstack_base = oldbase
#define RESERVE(x) if (vm->valstack_top+(x) > vm->stack_max) { stackOverflow(); } \
                   else { bzero(vm->valstack_top, (x)*sizeof(VAL)); }
#define ADDTOP(x) vm->valstack_top += (x)
#define TOPBASE(x) vm->valstack_top = vm->valstack_base + (x)
#define BASETOP(x) vm->valstack_base = vm->valstack_top + (x)
#define STOREOLD myoldbase = vm->valstack_base

#define CALL(f) f(vm, myoldbase);
#define TAILCALL(f) f(vm, oldbase);

// Creating new values (each value placed at the top of the stack)
VAL MKFLOAT(VM* vm, double val);
VAL MKSTR(VM* vm, char* str);
VAL MKPTR(VM* vm, void* ptr);

VAL MKCON(VM* vm, VAL cl, int tag, int arity, ...);

#define SETTAG(x, a) (x)->info.c.tag = (a)
#define SETARG(x, i, a) ((x)->info.c.args)[i] = ((VAL)(a))

void PROJECT(VM* vm, VAL r, int loc, int arity); 
void SLIDE(VM* vm, int args);

void* allocate(VM* vm, size_t size);
void* allocCon(VM* vm, int arity);

void dumpVal(VAL r);
void dumpStack(VM* vm);

// Casts

#define idris_castIntFloat(x) MKFLOAT(vm, (double)(GETINT(x)))
#define idris_castFloatInt(x) MKINT((i_int)(GETFLOAT(x)))

VAL idris_castIntStr(VM* vm, VAL i);
VAL idris_castStrInt(VM* vm, VAL i);
VAL idris_castFloatStr(VM* vm, VAL i);
VAL idris_castStrFloat(VM* vm, VAL i);

// String primitives

VAL idris_concat(VM* vm, VAL l, VAL r);
VAL idris_strlt(VM* vm, VAL l, VAL r);
VAL idris_streq(VM* vm, VAL l, VAL r);
VAL idris_strlen(VM* vm, VAL l);
VAL idris_readStr(VM* vm, FILE* h);

VAL idris_strHead(VM* vm, VAL str);
VAL idris_strTail(VM* vm, VAL str);
VAL idris_strCons(VM* vm, VAL x, VAL xs);
VAL idris_strIndex(VM* vm, VAL str, VAL i);
VAL idris_strRev(VM* vm, VAL str);

// Handle stack overflow. 
// Just reports an error and exits.

void stackOverflow();

#include "idris_gmp.h"

#endif 
