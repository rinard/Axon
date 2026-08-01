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
  mov x0, #0
  str x0, [sp, #32]
.L4:
  mov x0, #0
  str x0, [sp, #40]
.L5:
  mov x0, #5
  str x0, [sp, #8]
.L6:
  mov x0, #10
  str x0, [sp, #48]
.L7:
  ldr x1, [sp, #8]
  ldr x2, [sp, #48]
  cmp x1, x2
  cset w0, lt
  str x0, [sp, #16]
.L8:
  mov x0, #5
  str x0, [sp, #56]
.L9:
  ldr x1, [sp, #8]
  ldr x2, [sp, #56]
  cmp x1, x2
  cset w0, eq
  str x0, [sp, #24]
.L10:
  mov x0, #3
  str x0, [sp, #64]
.L11:
  ldr x1, [sp, #8]
  ldr x2, [sp, #64]
  cmp x1, x2
  cset w0, lt
  cbnz w0, .L16
.L12:
  mov x0, #4
  str x0, [sp, #72]
.L13:
  ldr x1, [sp, #72]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  cbnz w0, .L16
.L14:
  mov x0, #0
  str x0, [sp, #80]
.L15:
  b .L17
.L16:
  mov x0, #1
  str x0, [sp, #80]
.L17:
  ldr x1, [sp, #80]
  mov x2, #0
  cmp x1, x2
  cset w0, ne
  str x0, [sp, #32]
.L18:
  ldr x0, [sp, #16]
  and w0, w0, #1
  eor w0, w0, #1
  cbnz w0, .L22
.L19:
  ldr x0, [sp, #24]
  and w0, w0, #1
  eor w0, w0, #1
  cbnz w0, .L22
.L20:
  mov x0, #1
  str x0, [sp, #88]
.L21:
  b .L23
.L22:
  mov x0, #0
  str x0, [sp, #88]
.L23:
  ldr x1, [sp, #88]
  mov x2, #0
  cmp x1, x2
  cset w0, ne
  str x0, [sp, #40]
.L24:
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
  // print a
  ldr x9, [sp, #16]
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
  ldr x9, [sp, #24]
  sub sp, sp, #16
  adrp x8, .Lname_b@PAGE
  add x8, x8, .Lname_b@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print c
  ldr x9, [sp, #32]
  sub sp, sp, #16
  adrp x8, .Lname_c@PAGE
  add x8, x8, .Lname_c@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print d
  ldr x9, [sp, #40]
  sub sp, sp, #16
  adrp x8, .Lname_d@PAGE
  add x8, x8, .Lname_d@PAGEOFF
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
.Lname_x:
  .asciz "x"
.Lname_a:
  .asciz "a"
.Lname_b:
  .asciz "b"
.Lname_c:
  .asciz "c"
.Lname_d:
  .asciz "d"
