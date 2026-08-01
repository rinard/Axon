.global _main
.align 2

_main:
  sub sp, sp, #80
  str x30, [sp, #72]
  str x29, [sp, #64]
  add x29, sp, #64

  // Initialize all variables to 0
  mov x0, #0

  str x0, [sp, #8]
  str x0, [sp, #16]
  str x0, [sp, #24]
  str x0, [sp, #32]
  str x0, [sp, #40]
  str x0, [sp, #48]

.L0:
  mov x0, #0
  str x0, [sp, #8]
.L1:
  mov x0, #0
  str x0, [sp, #16]
.L2:
  mov x0, #5
  str x0, [sp, #8]
.L3:
  mov x0, #0
  str x0, [sp, #16]
.L4:
  mov x0, #0
  str x0, [sp, #24]
.L5:
  ldr x1, [sp, #24]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L12
.L6:
  mov x0, #100
  str x0, [sp, #32]
.L7:
  ldr x2, [sp, #8]
  cbz x2, .Ldiv_by_zero
  ldr x1, [sp, #32]
  ldr x2, [sp, #8]
  sdiv x0, x1, x2
  str x0, [sp, #40]
.L8:
  ldr x1, [sp, #16]
  ldr x2, [sp, #40]
  add x0, x1, x2
  str x0, [sp, #16]
.L9:
  mov x0, #1
  str x0, [sp, #48]
.L10:
  ldr x1, [sp, #8]
  ldr x2, [sp, #48]
  sub x0, x1, x2
  str x0, [sp, #8]
.L11:
  b .L4
.L12:
  b .Lhalt

.Lhalt:
  // Print observable variables
  // print i
  ldr x9, [sp, #8]
  sub sp, sp, #16
  adrp x8, .Lname_i@PAGE
  add x8, x8, .Lname_i@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print s
  ldr x9, [sp, #16]
  sub sp, sp, #16
  adrp x8, .Lname_s@PAGE
  add x8, x8, .Lname_s@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16

  // Exit with code 0
  mov x0, #0
  ldr x29, [sp, #64]
  ldr x30, [sp, #72]
  add sp, sp, #80
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
.Lname_i:
  .asciz "i"
.Lname_s:
  .asciz "s"
