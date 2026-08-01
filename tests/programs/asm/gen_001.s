.global _main
.align 2

_main:
  sub sp, sp, #272
  str x30, [sp, #264]
  str x29, [sp, #256]
  add x29, sp, #256

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
  str x0, [sp, #160]
  str x0, [sp, #168]
  str x0, [sp, #176]
  str x0, [sp, #184]
  str x0, [sp, #192]
  str x0, [sp, #200]
  str x0, [sp, #208]
  str x0, [sp, #216]
  str x0, [sp, #224]
  str x0, [sp, #232]
  str x0, [sp, #240]

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
  mov x0, #0
  str x0, [sp, #64]
.L8:
  mov x0, #2
  str x0, [sp, #40]
.L9:
  mov x0, #42
  str x0, [sp, #16]
.L10:
  mov x0, #10
  str x0, [sp, #48]
.L11:
  mov x0, #0
  str x0, [sp, #72]
.L12:
  mov x0, #0
  str x0, [sp, #80]
.L13:
  mov x0, #5
  str x0, [sp, #88]
.L14:
  ldr x1, [sp, #80]
  ldr x2, [sp, #88]
  sub x0, x1, x2
  str x0, [sp, #96]
.L15:
  ldr x1, [sp, #72]
  cmp x1, #32
  b.hs .Lbounds_err
  ldr x2, [sp, #96]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L16:
  mov x0, #1
  str x0, [sp, #104]
.L17:
  mov x0, #100
  str x0, [sp, #112]
.L18:
  ldr x1, [sp, #104]
  cmp x1, #32
  b.hs .Lbounds_err
  ldr x2, [sp, #112]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L19:
  mov x0, #2
  str x0, [sp, #120]
.L20:
  mov x0, #3
  str x0, [sp, #128]
.L21:
  ldr x1, [sp, #120]
  cmp x1, #32
  b.hs .Lbounds_err
  ldr x2, [sp, #128]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L22:
  mov x0, #0
  str x0, [sp, #136]
.L23:
  mov x0, #0
  str x0, [sp, #144]
.L24:
  ldr x1, [sp, #136]
  cmp x1, #32
  b.hs .Lbounds_err
  ldr x2, [sp, #144]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L25:
  mov x0, #1
  str x0, [sp, #152]
.L26:
  mov x0, #3
  str x0, [sp, #160]
.L27:
  ldr x1, [sp, #152]
  cmp x1, #32
  b.hs .Lbounds_err
  ldr x2, [sp, #160]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L28:
  mov x0, #2
  str x0, [sp, #168]
.L29:
  mov x0, #0
  str x0, [sp, #176]
.L30:
  ldr x1, [sp, #168]
  cmp x1, #32
  b.hs .Lbounds_err
  ldr x2, [sp, #176]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L31:
  mov x0, #5
  str x0, [sp, #184]
.L32:
  ldr x1, [sp, #32]
  ldr x2, [sp, #184]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L37
.L33:
  ldr x1, [sp, #48]
  ldr x2, [sp, #48]
  sub x0, x1, x2
  str x0, [sp, #40]
.L34:
  mov x0, #1
  str x0, [sp, #192]
.L35:
  ldr x1, [sp, #32]
  ldr x2, [sp, #192]
  add x0, x1, x2
  str x0, [sp, #32]
.L36:
  b .L31
.L37:
  ldr x0, [sp, #40]
  str x0, [sp, #16]
.L38:
  mov x0, #32
  str x0, [sp, #200]
.L39:
  ldr x2, [sp, #200]
  cbz x2, .Ldiv_by_zero
  ldr x1, [sp, #32]
  ldr x2, [sp, #200]
  sdiv x3, x1, x2
  msub x0, x3, x2, x1
  str x0, [sp, #208]
.L40:
  mov x0, #32
  str x0, [sp, #216]
.L41:
  ldr x1, [sp, #208]
  ldr x2, [sp, #216]
  add x0, x1, x2
  str x0, [sp, #224]
.L42:
  mov x0, #32
  str x0, [sp, #232]
.L43:
  ldr x2, [sp, #232]
  cbz x2, .Ldiv_by_zero
  ldr x1, [sp, #224]
  ldr x2, [sp, #232]
  sdiv x3, x1, x2
  msub x0, x3, x2, x1
  str x0, [sp, #240]
.L44:
  ldr x1, [sp, #240]
  cmp x1, #32
  b.hs .Lbounds_err
  ldr x2, [sp, #16]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L45:
  b .Lhalt

.Lhalt:
  // Print observable variables
  // print v0
  ldr x9, [sp, #8]
  sub sp, sp, #16
  adrp x8, .Lname_v0@PAGE
  add x8, x8, .Lname_v0@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print v1
  ldr x9, [sp, #16]
  sub sp, sp, #16
  adrp x8, .Lname_v1@PAGE
  add x8, x8, .Lname_v1@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print v2
  ldr x9, [sp, #24]
  sub sp, sp, #16
  adrp x8, .Lname_v2@PAGE
  add x8, x8, .Lname_v2@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print v3
  ldr x9, [sp, #32]
  sub sp, sp, #16
  adrp x8, .Lname_v3@PAGE
  add x8, x8, .Lname_v3@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print v4
  ldr x9, [sp, #40]
  sub sp, sp, #16
  adrp x8, .Lname_v4@PAGE
  add x8, x8, .Lname_v4@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print v5
  ldr x9, [sp, #48]
  sub sp, sp, #16
  adrp x8, .Lname_v5@PAGE
  add x8, x8, .Lname_v5@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print b0
  ldr x9, [sp, #56]
  sub sp, sp, #16
  adrp x8, .Lname_b0@PAGE
  add x8, x8, .Lname_b0@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print b1
  ldr x9, [sp, #64]
  sub sp, sp, #16
  adrp x8, .Lname_b1@PAGE
  add x8, x8, .Lname_b1@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16

  // Exit with code 0
  mov x0, #0
  ldr x29, [sp, #256]
  ldr x30, [sp, #264]
  add sp, sp, #272
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
.Lname_v0:
  .asciz "v0"
.Lname_v1:
  .asciz "v1"
.Lname_v2:
  .asciz "v2"
.Lname_v3:
  .asciz "v3"
.Lname_v4:
  .asciz "v4"
.Lname_v5:
  .asciz "v5"
.Lname_b0:
  .asciz "b0"
.Lname_b1:
  .asciz "b1"

.section __DATA,__data
.global _arr_A
.align 3
_arr_A:
  .space 8192
.global _arr_B
.align 3
_arr_B:
  .space 8192
