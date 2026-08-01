.global _main
.align 2

_main:
  sub sp, sp, #112
  str x30, [sp, #104]
  str x29, [sp, #96]
  add x29, sp, #96

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
  str x0, [sp, #80]
  str x0, [sp, #88]

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
  mov x0, #64
  str x0, [sp, #8]
.L4:
  mov x0, #0
  str x0, [sp, #16]
.L5:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L14
.L6:
  mov x0, #1
  str x0, [sp, #32]
.L7:
  ldr x1, [sp, #16]
  ldr x2, [sp, #32]
  add x0, x1, x2
  str x0, [sp, #40]
.L8:
  ldr x1, [sp, #16]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #40]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L9:
  ldr x1, [sp, #8]
  ldr x2, [sp, #16]
  sub x0, x1, x2
  str x0, [sp, #48]
.L10:
  ldr x1, [sp, #16]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #48]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L11:
  mov x0, #1
  str x0, [sp, #56]
.L12:
  ldr x1, [sp, #16]
  ldr x2, [sp, #56]
  add x0, x1, x2
  str x0, [sp, #16]
.L13:
  b .L5
.L14:
  mov x0, #0
  str x0, [sp, #24]
.L15:
  mov x0, #0
  str x0, [sp, #16]
.L16:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L24
.L17:
  ldr x1, [sp, #16]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #64]
.L18:
  ldr x1, [sp, #16]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #72]
.L19:
  ldr x1, [sp, #64]
  ldr x2, [sp, #72]
  mul x0, x1, x2
  str x0, [sp, #80]
.L20:
  ldr x1, [sp, #24]
  ldr x2, [sp, #80]
  add x0, x1, x2
  str x0, [sp, #24]
.L21:
  mov x0, #1
  str x0, [sp, #88]
.L22:
  ldr x1, [sp, #16]
  ldr x2, [sp, #88]
  add x0, x1, x2
  str x0, [sp, #16]
.L23:
  b .L16
.L24:
  b .Lhalt

.Lhalt:
  // Print observable variables
  // print n
  ldr x9, [sp, #8]
  sub sp, sp, #16
  adrp x8, .Lname_n@PAGE
  add x8, x8, .Lname_n@PAGEOFF
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
  // print dot
  ldr x9, [sp, #24]
  sub sp, sp, #16
  adrp x8, .Lname_dot@PAGE
  add x8, x8, .Lname_dot@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16

  // Exit with code 0
  mov x0, #0
  ldr x29, [sp, #96]
  ldr x30, [sp, #104]
  add sp, sp, #112
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
.Lname_n:
  .asciz "n"
.Lname_i:
  .asciz "i"
.Lname_dot:
  .asciz "dot"

.section __DATA,__data
.global _arr_A
.align 3
_arr_A:
  .space 8192
.global _arr_B
.align 3
_arr_B:
  .space 8192
