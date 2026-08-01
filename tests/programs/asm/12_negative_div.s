.global _main
.align 2

_main:
  sub sp, sp, #160
  str x30, [sp, #152]
  str x29, [sp, #144]
  add x29, sp, #144

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
  str x0, [sp, #96]
  str x0, [sp, #104]
  str x0, [sp, #112]
  str x0, [sp, #120]
  str x0, [sp, #128]

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
  mov x0, #0
  str x0, [sp, #48]
.L6:
  mov x0, #0
  str x0, [sp, #56]
.L7:
  mov x0, #17
  str x0, [sp, #64]
.L8:
  ldr x1, [sp, #56]
  ldr x2, [sp, #64]
  sub x0, x1, x2
  str x0, [sp, #8]
.L9:
  mov x0, #5
  str x0, [sp, #16]
.L10:
  ldr x2, [sp, #16]
  cbz x2, .Ldiv_by_zero
  ldr x1, [sp, #8]
  ldr x2, [sp, #16]
  sdiv x0, x1, x2
  str x0, [sp, #24]
.L11:
  ldr x2, [sp, #16]
  cbz x2, .Ldiv_by_zero
  ldr x1, [sp, #8]
  ldr x2, [sp, #16]
  sdiv x3, x1, x2
  msub x0, x3, x2, x1
  str x0, [sp, #32]
.L12:
  mov x0, #17
  str x0, [sp, #72]
.L13:
  mov x0, #0
  str x0, [sp, #80]
.L14:
  mov x0, #5
  str x0, [sp, #88]
.L15:
  ldr x1, [sp, #80]
  ldr x2, [sp, #88]
  sub x0, x1, x2
  str x0, [sp, #96]
.L16:
  ldr x2, [sp, #96]
  cbz x2, .Ldiv_by_zero
  ldr x1, [sp, #72]
  ldr x2, [sp, #96]
  sdiv x0, x1, x2
  str x0, [sp, #40]
.L17:
  mov x0, #17
  str x0, [sp, #104]
.L18:
  mov x0, #0
  str x0, [sp, #112]
.L19:
  mov x0, #5
  str x0, [sp, #120]
.L20:
  ldr x1, [sp, #112]
  ldr x2, [sp, #120]
  sub x0, x1, x2
  str x0, [sp, #128]
.L21:
  ldr x2, [sp, #128]
  cbz x2, .Ldiv_by_zero
  ldr x1, [sp, #104]
  ldr x2, [sp, #128]
  sdiv x3, x1, x2
  msub x0, x3, x2, x1
  str x0, [sp, #48]
.L22:
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
  // print q
  ldr x9, [sp, #24]
  sub sp, sp, #16
  adrp x8, .Lname_q@PAGE
  add x8, x8, .Lname_q@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print r
  ldr x9, [sp, #32]
  sub sp, sp, #16
  adrp x8, .Lname_r@PAGE
  add x8, x8, .Lname_r@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print q2
  ldr x9, [sp, #40]
  sub sp, sp, #16
  adrp x8, .Lname_q2@PAGE
  add x8, x8, .Lname_q2@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print r2
  ldr x9, [sp, #48]
  sub sp, sp, #16
  adrp x8, .Lname_r2@PAGE
  add x8, x8, .Lname_r2@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16

  // Exit with code 0
  mov x0, #0
  ldr x29, [sp, #144]
  ldr x30, [sp, #152]
  add sp, sp, #160
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
.Lname_q:
  .asciz "q"
.Lname_r:
  .asciz "r"
.Lname_q2:
  .asciz "q2"
.Lname_r2:
  .asciz "r2"
