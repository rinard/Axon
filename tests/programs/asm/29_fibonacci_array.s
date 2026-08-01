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
  mov x0, #20
  str x0, [sp, #8]
.L4:
  mov x0, #0
  str x0, [sp, #32]
.L5:
  mov x0, #0
  str x0, [sp, #40]
.L6:
  ldr x1, [sp, #32]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #40]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L7:
  mov x0, #1
  str x0, [sp, #48]
.L8:
  mov x0, #1
  str x0, [sp, #56]
.L9:
  ldr x1, [sp, #48]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #56]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L10:
  mov x0, #2
  str x0, [sp, #16]
.L11:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L23
.L12:
  mov x0, #1
  str x0, [sp, #64]
.L13:
  ldr x1, [sp, #16]
  ldr x2, [sp, #64]
  sub x0, x1, x2
  str x0, [sp, #72]
.L14:
  ldr x1, [sp, #72]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #80]
.L15:
  mov x0, #2
  str x0, [sp, #88]
.L16:
  ldr x1, [sp, #16]
  ldr x2, [sp, #88]
  sub x0, x1, x2
  str x0, [sp, #96]
.L17:
  ldr x1, [sp, #96]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #104]
.L18:
  ldr x1, [sp, #80]
  ldr x2, [sp, #104]
  add x0, x1, x2
  str x0, [sp, #112]
.L19:
  ldr x1, [sp, #16]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #112]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L20:
  mov x0, #1
  str x0, [sp, #120]
.L21:
  ldr x1, [sp, #16]
  ldr x2, [sp, #120]
  add x0, x1, x2
  str x0, [sp, #16]
.L22:
  b .L11
.L23:
  ldr x1, [sp, #8]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #128]
.L24:
  ldr x0, [sp, #128]
  str x0, [sp, #24]
.L25:
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
  // print r
  ldr x9, [sp, #24]
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
.Lname_n:
  .asciz "n"
.Lname_i:
  .asciz "i"
.Lname_r:
  .asciz "r"

.section __DATA,__data
.global _arr_A
.align 3
_arr_A:
  .space 8192
