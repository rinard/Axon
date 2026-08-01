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
  str x0, [sp, #40]

.L0:
  mov x0, #0
  str x0, [sp, #8]
.L1:
  mov x0, #0
  str x0, [sp, #16]
.L2:
  mov x0, #0
  str x0, [sp, #8]
.L3:
  mov x0, #10
  str x0, [sp, #16]
.L4:
  mov x0, #5
  str x0, [sp, #24]
.L5:
  ldr x1, [sp, #16]
  ldr x2, [sp, #24]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L11
.L6:
  mov x0, #1
  str x0, [sp, #32]
.L7:
  ldr x1, [sp, #8]
  ldr x2, [sp, #32]
  add x0, x1, x2
  str x0, [sp, #8]
.L8:
  mov x0, #1
  str x0, [sp, #40]
.L9:
  ldr x1, [sp, #16]
  ldr x2, [sp, #40]
  add x0, x1, x2
  str x0, [sp, #16]
.L10:
  b .L4
.L11:
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
  // print i
  ldr x9, [sp, #16]
  sub sp, sp, #16
  adrp x8, .Lname_i@PAGE
  add x8, x8, .Lname_i@PAGEOFF
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
.Lname_i:
  .asciz "i"
