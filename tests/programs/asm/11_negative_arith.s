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
  mov x0, #100
  str x0, [sp, #56]
.L7:
  ldr x1, [sp, #48]
  ldr x2, [sp, #56]
  sub x0, x1, x2
  str x0, [sp, #8]
.L8:
  mov x0, #0
  str x0, [sp, #64]
.L9:
  mov x0, #200
  str x0, [sp, #72]
.L10:
  ldr x1, [sp, #64]
  ldr x2, [sp, #72]
  sub x0, x1, x2
  str x0, [sp, #16]
.L11:
  ldr x1, [sp, #8]
  ldr x2, [sp, #16]
  add x0, x1, x2
  str x0, [sp, #24]
.L12:
  ldr x1, [sp, #8]
  ldr x2, [sp, #16]
  mul x0, x1, x2
  str x0, [sp, #32]
.L13:
  ldr x1, [sp, #8]
  ldr x2, [sp, #16]
  sub x0, x1, x2
  str x0, [sp, #40]
.L14:
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
  // print c
  ldr x9, [sp, #24]
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
  ldr x9, [sp, #32]
  sub sp, sp, #16
  adrp x8, .Lname_d@PAGE
  add x8, x8, .Lname_d@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print e
  ldr x9, [sp, #40]
  sub sp, sp, #16
  adrp x8, .Lname_e@PAGE
  add x8, x8, .Lname_e@PAGEOFF
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
.Lname_a:
  .asciz "a"
.Lname_b:
  .asciz "b"
.Lname_c:
  .asciz "c"
.Lname_d:
  .asciz "d"
.Lname_e:
  .asciz "e"
