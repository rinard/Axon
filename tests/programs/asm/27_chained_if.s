.global _main
.align 2

_main:
  sub sp, sp, #64
  str x30, [sp, #56]
  str x29, [sp, #48]
  add x29, sp, #48

  // Initialize all variables to 0
  mov x0, #0

  str x0, [sp, #8]
  str x0, [sp, #16]
  str x0, [sp, #24]
  str x0, [sp, #32]

.L0:
  mov x0, #0
  str x0, [sp, #8]
.L1:
  mov x0, #0
  str x0, [sp, #16]
.L2:
  mov x0, #42
  str x0, [sp, #8]
.L3:
  mov x0, #10
  str x0, [sp, #24]
.L4:
  ldr x1, [sp, #8]
  ldr x2, [sp, #24]
  cmp x1, x2
  cset w0, lt
  cbnz w0, .L11
.L5:
  mov x0, #50
  str x0, [sp, #32]
.L6:
  ldr x1, [sp, #8]
  ldr x2, [sp, #32]
  cmp x1, x2
  cset w0, lt
  cbnz w0, .L9
.L7:
  mov x0, #3
  str x0, [sp, #16]
.L8:
  b .L10
.L9:
  mov x0, #2
  str x0, [sp, #16]
.L10:
  b .L12
.L11:
  mov x0, #1
  str x0, [sp, #16]
.L12:
  b .Lhalt

.Lhalt:
  // Print observable variables
  // print x
  ldr x9, [sp, #8]
  sub sp, sp, #16
  adrp x8, .Lname_x@PAGE
  add x8, x8, .Lname_x@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print r
  ldr x9, [sp, #16]
  sub sp, sp, #16
  adrp x8, .Lname_r@PAGE
  add x8, x8, .Lname_r@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16

  // Exit with code 0
  mov x0, #0
  ldr x29, [sp, #48]
  ldr x30, [sp, #56]
  add sp, sp, #64
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
.Lname_x:
  .asciz "x"
.Lname_r:
  .asciz "r"
