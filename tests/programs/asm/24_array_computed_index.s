.global _main
.align 2

_main:
  sub sp, sp, #96
  str x30, [sp, #88]
  str x29, [sp, #80]
  add x29, sp, #80

  // Initialize all variables to 0
  mov x0, #0

  str x0, [sp, #8]
  str x0, [sp, #16]
  str x0, [sp, #24]
  str x0, [sp, #32]
  str x0, [sp, #40]
  str x0, [sp, #48]
  str x0, [sp, #56]
  str x0, [sp, #64]
  str x0, [sp, #72]

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
  str x0, [sp, #24]
.L4:
  ldr x1, [sp, #8]
  ldr x2, [sp, #24]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L10
.L5:
  ldr x1, [sp, #8]
  ldr x2, [sp, #8]
  mul x0, x1, x2
  str x0, [sp, #32]
.L6:
  ldr x1, [sp, #8]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #32]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L7:
  mov x0, #1
  str x0, [sp, #40]
.L8:
  ldr x1, [sp, #8]
  ldr x2, [sp, #40]
  add x0, x1, x2
  str x0, [sp, #8]
.L9:
  b .L3
.L10:
  mov x0, #3
  str x0, [sp, #48]
.L11:
  ldr x1, [sp, #48]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #56]
.L12:
  mov x0, #7
  str x0, [sp, #64]
.L13:
  ldr x1, [sp, #64]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #72]
.L14:
  ldr x1, [sp, #56]
  ldr x2, [sp, #72]
  add x0, x1, x2
  str x0, [sp, #16]
.L15:
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
  ldr x29, [sp, #80]
  ldr x30, [sp, #88]
  add sp, sp, #96
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

.section __DATA,__data
.global _arr_A
.align 3
_arr_A:
  .space 8192
