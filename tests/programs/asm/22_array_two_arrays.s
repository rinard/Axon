.global _main
.align 2

_main:
  sub sp, sp, #176
  str x30, [sp, #168]
  str x29, [sp, #160]
  add x29, sp, #160

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
  str x0, [sp, #136]
  str x0, [sp, #144]
  str x0, [sp, #152]

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
  mov x0, #1
  str x0, [sp, #32]
.L4:
  ldr x1, [sp, #24]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #32]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L5:
  mov x0, #1
  str x0, [sp, #40]
.L6:
  mov x0, #2
  str x0, [sp, #48]
.L7:
  ldr x1, [sp, #40]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #48]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L8:
  mov x0, #2
  str x0, [sp, #56]
.L9:
  mov x0, #3
  str x0, [sp, #64]
.L10:
  ldr x1, [sp, #56]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #64]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L11:
  mov x0, #0
  str x0, [sp, #72]
.L12:
  mov x0, #10
  str x0, [sp, #80]
.L13:
  ldr x1, [sp, #72]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #80]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L14:
  mov x0, #1
  str x0, [sp, #88]
.L15:
  mov x0, #20
  str x0, [sp, #96]
.L16:
  ldr x1, [sp, #88]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #96]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L17:
  mov x0, #2
  str x0, [sp, #104]
.L18:
  mov x0, #30
  str x0, [sp, #112]
.L19:
  ldr x1, [sp, #104]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #112]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L20:
  mov x0, #0
  str x0, [sp, #16]
.L21:
  mov x0, #0
  str x0, [sp, #8]
.L22:
  mov x0, #3
  str x0, [sp, #120]
.L23:
  ldr x1, [sp, #8]
  ldr x2, [sp, #120]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L31
.L24:
  ldr x1, [sp, #8]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #128]
.L25:
  ldr x1, [sp, #8]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #136]
.L26:
  ldr x1, [sp, #128]
  ldr x2, [sp, #136]
  mul x0, x1, x2
  str x0, [sp, #144]
.L27:
  ldr x1, [sp, #16]
  ldr x2, [sp, #144]
  add x0, x1, x2
  str x0, [sp, #16]
.L28:
  mov x0, #1
  str x0, [sp, #152]
.L29:
  ldr x1, [sp, #8]
  ldr x2, [sp, #152]
  add x0, x1, x2
  str x0, [sp, #8]
.L30:
  b .L22
.L31:
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
  ldr x29, [sp, #160]
  ldr x30, [sp, #168]
  add sp, sp, #176
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
.global _arr_B
.align 3
_arr_B:
  .space 8192
