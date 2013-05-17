target datalayout = "e-p:64:64:64-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:64:64-f32:32:32-f64:64:64-v64:64:64-v128:128:128-a0:0:64-s0:64:64-f80:128:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@unit = private unnamed_addr constant i8 -1

declare double    @llvm.sqrt.f64(double %Val)
declare double    @llvm.sin.f64(double %Val)
declare double    @llvm.cos.f64(double %Val)
declare double    @llvm.pow.f64(double %Val, double %Power)
declare double    @llvm.exp.f64(double %Val)
declare double    @llvm.log.f64(double %Val)
declare double    @llvm.fabs.f64(double %Val)
declare double    @llvm.floor.f64(double %Val)
declare double    @llvm.ceil.f64(double %Val)
declare double    @llvm.trunc.f64(double %Val)

declare {}* @llvm.invariant.start(i64, i8* nocapture)
declare void @llvm.memcpy.p0i8.p0i8.i64(i8*, i8*, i64, i32, i1)
declare void @llvm.memset.p0i8.i32(i8*, i8, i32, i32, i1)
declare void @llvm.memmove.p0i8.p0i8.i32(i8*, i8*, i32, i32, i1)
declare void @llvm.trap() noreturn nounwind
declare i32 @printf(i8* nocapture, ...) nounwind
declare i8* @fgets(i8*, i32, i8* nocapture) nounwind
declare noalias i8* @GC_malloc(i64)
declare noalias i8* @GC_malloc_atomic(i64)
declare i8* @GC_realloc(i8*, i64)
declare void @GC_free(i8*)

%mpz = type { i32, i32, i64* }
declare void @__gmp_set_memory_functions(i8* (i64)*, i8* (i8*, i64, i64)*, void (i8*, i64)*)
declare void @__gmpz_init(%mpz*)
declare i64 @__gmpz_get_si(%mpz*)
declare void @__gmpz_set(%mpz*, %mpz*)
declare void @__gmpz_init_set(%mpz*, %mpz*)
declare void @__gmpz_init_set_si(%mpz*, i64)
declare i32 @__gmpz_init_set_str(%mpz*, i8*, i32)
declare void @__gmpz_add(%mpz*, %mpz*, %mpz*)
declare void @__gmpz_sub(%mpz*, %mpz*, %mpz*)
declare void @__gmpz_mul(%mpz*, %mpz*, %mpz*)
declare void @__gmpz_fdiv_q(%mpz*, %mpz*, %mpz*)
declare void @__gmpz_fdiv_r(%mpz*, %mpz*, %mpz*)
declare void @__gmpz_mod(%mpz*, %mpz*, %mpz*)
declare void @__gmpz_and(%mpz*, %mpz*, %mpz*)
declare void @__gmpz_ior(%mpz*, %mpz*, %mpz*)
declare void @__gmpz_xor(%mpz*, %mpz*, %mpz*)
declare void @__gmpz_com(%mpz*, %mpz*)
declare i32 @__gmpz_cmp_si(%mpz*, i64) nounwind readonly
declare i32 @__gmpz_cmp(%mpz*, %mpz*) nounwind readonly
declare i8* @__gmpz_get_str(i8*, i32, %mpz*)

@emptyStr = private unnamed_addr constant [1 x i8] zeroinitializer, align 1
@strfmt = private unnamed_addr constant [3 x i8] c"%s\00", align 1
@intfmt = private unnamed_addr constant [4 x i8] c"%ld\00", align 1

define internal i8* @gmp_realloc(i8* %ptr, i64 %old, i64 %new) {
  %1 = tail call i8* @GC_realloc(i8* %ptr, i64 %new)
  ret i8* %1
}

define internal void @gmp_free(i8* %ptr, i64 %size) {
  tail call void @GC_free(i8* %ptr)
  ret void
}

define internal void @idris_memset(i8* %ptr, i32 %off, i8 %val, i32 %len) {
  %1 = ptrtoint i8* %ptr to i64
  %2 = zext i32 %off to i64
  %3 = add i64 %1, %2
  %4 = inttoptr i64 %3 to i8*
  tail call void @llvm.memset.p0i8.i32(i8* %4, i8 %val, i32 %len, i32 0, i1 false)
  ret void
}

define internal void @idris_memmove(i8* %dest, i8* %src, i32 %doff, i32 %soff, i32 %len) {
  %1 = ptrtoint i8* %dest to i64
  %2 = zext i32 %doff to i64
  %3 = add i64 %1, %2
  %4 = inttoptr i64 %3 to i8*
  %5 = ptrtoint i8* %src to i64
  %6 = zext i32 %soff to i64
  %7 = add i64 %5, %6
  %8 = inttoptr i64 %7 to i8*
  tail call void @llvm.memmove.p0i8.p0i8.i32(i8* %4, i8* %8, i32 %len, i32 0, i1 false)
  ret void
}

define internal i8 @idris_peek(i8* %ptr, i32 %off) {
  %1 = ptrtoint i8* %ptr to i64
  %2 = zext i32 %off to i64
  %3 = add i64 %1, %2
  %4 = inttoptr i64 %3 to i8*
  %5 = load i8* %4, align 1
  ret i8 %5
}

define internal void @idris_poke(i8* %ptr, i32 %off, i8 %val) {
  %1 = ptrtoint i8* %ptr to i64
  %2 = zext i32 %off to i64
  %3 = add i64 %1, %2
  %4 = inttoptr i64 %3 to i8*
  store i8 %val, i8* %4, align 1
  ret void
}

define internal fastcc i8* @readStr(i8* nocapture %h) nounwind {
  %1 = tail call noalias i8* @GC_malloc_atomic(i64 256) nounwind
  %2 = getelementptr inbounds i8* %1, i64 255
  store i8 1, i8* %2, align 1
  %3 = tail call i8* @fgets(i8* %1, i32 256, i8* %h) nounwind
  %4 = icmp eq i8* %3, null
  br i1 %4, label %.critedge, label %.preheader

.preheader:                                       ; preds = %0, %11
  %indvars.iv = phi i64 [ %indvars.iv.next, %11 ], [ 256, %0 ]
  %line_ptr.0 = phi i8* [ %13, %11 ], [ %2, %0 ]
  %line_buf.0 = phi i8* [ %12, %11 ], [ %1, %0 ]
  %5 = load i8* %line_ptr.0, align 1
  %6 = icmp eq i8 %5, 0
  br i1 %6, label %7, label %.critedge

; <label>:7                                       ; preds = %.preheader
  %8 = getelementptr inbounds i8* %line_ptr.0, i64 -1
  %9 = load i8* %8, align 1
  %10 = icmp eq i8 %9, 10
  br i1 %10, label %.critedge, label %11

; <label>:11                                      ; preds = %7
  %indvars.iv.next = add i64 %indvars.iv, 256
  %12 = tail call i8* @GC_realloc(i8* %line_buf.0, i64 %indvars.iv.next) nounwind
  %.sum18 = or i64 %indvars.iv, 255
  %13 = getelementptr inbounds i8* %12, i64 %.sum18
  store i8 1, i8* %13, align 1
  %.sum17 = add i64 %indvars.iv, -1
  %14 = getelementptr inbounds i8* %12, i64 %.sum17
  %15 = tail call i8* @fgets(i8* %14, i32 257, i8* %h) nounwind
  %16 = icmp eq i8* %15, null
  br i1 %16, label %.critedge, label %.preheader

.critedge:                                        ; preds = %.preheader, %7, %11, %0
  %.0 = phi i8* [ getelementptr inbounds ([1 x i8]* @emptyStr, i64 0, i64 0), %0 ], [ %line_buf.0, %.preheader ], [ %line_buf.0, %7 ], [ getelementptr inbounds ([1 x i8]* @emptyStr, i64 0, i64 0), %11 ]
  ret i8* %.0
}

define void @putStr(i8* %str) nounwind {
  %1 = tail call i32 (i8*, ...)* @printf(i8* getelementptr inbounds ([3 x i8]* @strfmt, i64 0, i64 0), i8* %str) nounwind
  ret void
}

define internal fastcc i8* @strConcat(i8* %l, i8* %r) nounwind {
  %1 = call i64 @strlen(i8* %l) nounwind readonly
  %2 = call i64 @strlen(i8* %r) nounwind readonly
  %3 = add i64 %1, 1
  %4 = add i64 %3, %2
  %5 = call noalias i8* @GC_malloc_atomic(i64 %4) nounwind
  store i8 0, i8* %5, align 1
  %6 = call i8* @strcat(i8* %5, i8* %l) nounwind
  %7 = call i8* @strcat(i8* %5, i8* %r) nounwind
  ret i8* %5
}

define internal fastcc noalias i8* @intStr(i64 %i) nounwind {
  %1 = tail call noalias i8* @GC_malloc_atomic(i64 12) nounwind
  %2 = tail call i32 (i8*, i64, i8*, ...)* @snprintf(i8* %1, i64 12, i8* getelementptr inbounds ([4 x i8]* @intfmt, i64 0, i64 0), i64 %i) nounwind
  ret i8* %1
}

declare i64 @strtol(i8*, i8**, i32)

define internal fastcc i32 @strEq(i8* %l, i8* %r) nounwind {
  %1 = call i32 @strcmp(i8* %l, i8* %r) nounwind readonly
  %2 = icmp eq i32 0, %1
  %3 = zext i1 %2 to i32
  ret i32 %3
}

define internal fastcc i8* @strCons(i32 %c, i8* %s) nounwind {
  %1 = call i64 @strlen(i8* %s) nounwind readonly
  %2 = add i64 %1, 2
  %3 = call noalias i8* @GC_malloc_atomic(i64 %2) nounwind
  %4 = trunc i32 %c to i8
  store i8 %4, i8* %3
  %5 = getelementptr inbounds i8* %3, i64 1
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* %5, i8* %s, i64 %1, i32 1, i1 false)
  %6 = add i64 %1, 1
  %7 = getelementptr inbounds i8* %3, i64 %6
  store i8 0, i8* %7
  ret i8* %3
}

define internal fastcc i32 @strHead(i8* %str) readonly nounwind {
  %1 = load i8* %str
  %2 = zext i8 %1 to i32
  ret i32 %2
}

define internal fastcc i8* @strTail(i8* %str) readnone nounwind {
  %1 = getelementptr inbounds i8* %str, i64 1
  ret i8* %1
}

@stdin = external global i8*

define noalias i8* @fileOpen(i8* nocapture %name, i8* nocapture %mode) nounwind {
  %1 = tail call i8* @fopen(i8* %name, i8* %mode) nounwind
  ret i8* %1
}

declare noalias i8* @fopen(i8* nocapture, i8* nocapture) nounwind

define void @fileClose(i8* nocapture %h) nounwind {
  %1 = tail call i32 @fclose(i8* %h) nounwind
  ret void
}

declare i32 @fclose(i8* nocapture) nounwind

define i32 @fileEOF(i8* nocapture %h) nounwind {
  %1 = tail call i32 @feof(i8* %h) nounwind
  ret i32 %1
}

declare i32 @feof(i8* nocapture) nounwind

define i32 @fileError(i8* nocapture %h) nounwind readonly {
  %1 = tail call i32 @ferror(i8* %h) nounwind
  ret i32 %1
}

declare i32 @ferror(i8* nocapture) nounwind readonly

define void @fputStr(i8* nocapture %h, i8* nocapture %str) nounwind {
  %1 = tail call i32 @fputs(i8* %str, i8* %h) nounwind
  ret void
}

declare i32 @fputs(i8* nocapture, i8* nocapture) nounwind

define i32 @isNull(i8* %ptr) nounwind readnone {
  %1 = icmp eq i8* %ptr, null
  %2 = zext i1 %1 to i32
  ret i32 %2
}

declare i32 @snprintf(i8* nocapture, i64, i8* nocapture, ...) nounwind
declare i64 @strlen(i8* nocapture) nounwind readonly
declare i8* @strcat(i8*, i8* nocapture) nounwind
declare i32 @strcmp(i8* nocapture, i8* nocapture) nounwind readonly
