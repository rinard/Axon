.global _main
.align 2

_main:
  sub sp, sp, #208
  str x30, [sp, #200]
  str x29, [sp, #192]
  add x29, sp, #192

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
  mov x0, #4
  str x0, [sp, #8]
.L4:
  mov x0, #0
  str x0, [sp, #32]
.L5:
  mov x0, #11
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
  mov x0, #22
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
  str x0, [sp, #64]
.L11:
  mov x0, #33
  str x0, [sp, #72]
.L12:
  ldr x1, [sp, #64]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #72]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L13:
  mov x0, #3
  str x0, [sp, #80]
.L14:
  mov x0, #44
  str x0, [sp, #88]
.L15:
  ldr x1, [sp, #80]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #88]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L16:
  mov x0, #0
  str x0, [sp, #16]
.L17:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L23
.L18:
  ldr x1, [sp, #16]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #96]
.L19:
  ldr x1, [sp, #16]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #96]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L20:
  mov x0, #1
  str x0, [sp, #104]
.L21:
  ldr x1, [sp, #16]
  ldr x2, [sp, #104]
  add x0, x1, x2
  str x0, [sp, #16]
.L22:
  b .L17
.L23:
  mov x0, #0
  str x0, [sp, #112]
.L24:
  ldr x1, [sp, #112]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #120]
.L25:
  mov x0, #1
  str x0, [sp, #128]
.L26:
  ldr x1, [sp, #128]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #136]
.L27:
  ldr x1, [sp, #120]
  ldr x2, [sp, #136]
  add x0, x1, x2
  str x0, [sp, #144]
.L28:
  mov x0, #2
  str x0, [sp, #152]
.L29:
  ldr x1, [sp, #152]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #160]
.L30:
  ldr x1, [sp, #144]
  ldr x2, [sp, #160]
  add x0, x1, x2
  str x0, [sp, #168]
.L31:
  mov x0, #3
  str x0, [sp, #176]
.L32:
  ldr x1, [sp, #176]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #184]
.L33:
  ldr x1, [sp, #168]
  ldr x2, [sp, #184]
  add x0, x1, x2
  str x0, [sp, #24]
.L34:
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
  // print s
  ldr x9, [sp, #24]
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
  ldr x29, [sp, #192]
  ldr x30, [sp, #200]
  add sp, sp, #208
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
