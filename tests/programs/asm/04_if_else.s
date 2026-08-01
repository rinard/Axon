.global _main
.align 2

_main:
  sub sp, sp, #48
  str x30, [sp, #40]
  str x29, [sp, #32]
  add x29, sp, #32

  // Initialize all variables to 0
  mov x0, #0

  str x0, [sp, #8]
  str x0, [sp, #16]
  str x0, [sp, #24]

.L0:
  mov x0, #0
  str x0, [sp, #8]
.L1:
  mov x0, #0
  str x0, [sp, #16]
.L2:
  mov x0, #0
  str x0, [sp, #24]
.L3:
  mov x0, #7
  str x0, [sp, #8]
.L4:
  mov x0, #13
  str x0, [sp, #16]
.L5:
  ldr x1, [sp, #8]
  ldr x2, [sp, #16]
  cmp x1, x2
  cset w0, lt
  cbnz w0, .L8
.L6:
  ldr x0, [sp, #8]
  str x0, [sp, #24]
.L7:
  b .L9
.L8:
  ldr x0, [sp, #16]
  str x0, [sp, #24]
.L9:
  b .Lhalt

.Lhalt:
  // Print observable variables
  // print a
  ldr x9, [sp, #8]
  sub sp, sp, #16
  adrp x8, .Lname_a@PAGE
  add x8, x8, .Lname_a@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print b
  ldr x9, [sp, #16]
  sub sp, sp, #16
  adrp x8, .Lname_b@PAGE
  add x8, x8, .Lname_b@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print m
  ldr x9, [sp, #24]
  sub sp, sp, #16
  adrp x8, .Lname_m@PAGE
  add x8, x8, .Lname_m@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16

  // Exit with code 0
  mov x0, #0
  ldr x29, [sp, #32]
  ldr x30, [sp, #40]
  add sp, sp, #48
  ret

.Ldiv_by_zero:
  adrp x0, .Ldiv_msg@PAGE
  add x0, x0, .Ldiv_msg@PAGEOFF
  bl _printf
  mov x0, #1
  bl _exit

.Lbounds_err:
  adrp x0, .Lbounds_msg@PAGE
  add x0, x0, .Lbounds_msg@PAGEOFF
  bl _printf
  mov x0, #1
  bl _exit

.section __TEXT,__cstring
.Lfmt:
  .asciz "%s = %ld\n"
.Ldiv_msg:
  .asciz "error: division by zero\n"
.Lbounds_msg:
  .asciz "error: array index out of bounds\n"
.Lname_a:
  .asciz "a"
.Lname_b:
  .asciz "b"
.Lname_m:
  .asciz "m"
