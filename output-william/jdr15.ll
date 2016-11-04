; ModuleID = 'calc'
source_filename = "calc"
target triple = "x86_64-unknown-linux-gnu"

declare { i64, i1 } @llvm.sadd.with.overflow.i64(i64, i64)

declare { i64, i1 } @llvm.ssub.with.overflow.i64(i64, i64)

declare { i64, i1 } @llvm.smul.with.overflow.i64(i64, i64)

declare void @overflow_fail(i64)

define i64 @f(i64, i64, i64, i64, i64, i64) {
entry:
  %6 = alloca i64
  store i64 0, i64* %6
  %7 = alloca i64
  store i64 0, i64* %7
  %8 = alloca i64
  store i64 0, i64* %8
  %9 = alloca i64
  store i64 0, i64* %9
  %10 = alloca i64
  store i64 0, i64* %10
  %11 = alloca i64
  store i64 0, i64* %11
  %12 = alloca i64
  store i64 0, i64* %12
  %13 = alloca i64
  store i64 0, i64* %13
  %14 = alloca i64
  store i64 0, i64* %14
  %15 = alloca i64
  store i64 0, i64* %15
  %16 = call { i64, i1 } @llvm.sadd.with.overflow.i64(i64 %5, i64 0)
  %17 = extractvalue { i64, i1 } %16, 1
  %18 = extractvalue { i64, i1 } %16, 0
  br i1 %17, label %error, label %noerror

error:                                            ; preds = %entry
  call void @overflow_fail(i64 81)
  ret i64 0

noerror:                                          ; preds = %entry
  %19 = call { i64, i1 } @llvm.sadd.with.overflow.i64(i64 %4, i64 %18)
  %20 = extractvalue { i64, i1 } %19, 1
  %21 = extractvalue { i64, i1 } %19, 0
  br i1 %20, label %error1, label %noerror2

error1:                                           ; preds = %noerror
  call void @overflow_fail(i64 75)
  ret i64 0

noerror2:                                         ; preds = %noerror
  %22 = call { i64, i1 } @llvm.sadd.with.overflow.i64(i64 %3, i64 %21)
  %23 = extractvalue { i64, i1 } %22, 1
  %24 = extractvalue { i64, i1 } %22, 0
  br i1 %23, label %error3, label %noerror4

error3:                                           ; preds = %noerror2
  call void @overflow_fail(i64 69)
  ret i64 0

noerror4:                                         ; preds = %noerror2
  %25 = call { i64, i1 } @llvm.sadd.with.overflow.i64(i64 %2, i64 %24)
  %26 = extractvalue { i64, i1 } %25, 1
  %27 = extractvalue { i64, i1 } %25, 0
  br i1 %26, label %error5, label %noerror6

error5:                                           ; preds = %noerror4
  call void @overflow_fail(i64 63)
  ret i64 0

noerror6:                                         ; preds = %noerror4
  %28 = call { i64, i1 } @llvm.sadd.with.overflow.i64(i64 %1, i64 %27)
  %29 = extractvalue { i64, i1 } %28, 1
  %30 = extractvalue { i64, i1 } %28, 0
  br i1 %29, label %error7, label %noerror8

error7:                                           ; preds = %noerror6
  call void @overflow_fail(i64 57)
  ret i64 0

noerror8:                                         ; preds = %noerror6
  %31 = call { i64, i1 } @llvm.sadd.with.overflow.i64(i64 %0, i64 %30)
  %32 = extractvalue { i64, i1 } %31, 1
  %33 = extractvalue { i64, i1 } %31, 0
  br i1 %32, label %error9, label %noerror10

error9:                                           ; preds = %noerror8
  call void @overflow_fail(i64 51)
  ret i64 0

noerror10:                                        ; preds = %noerror8
  ret i64 %33
}