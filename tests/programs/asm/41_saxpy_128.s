.global _main
.align 2

_main:
  sub sp, sp, #192
  str x30, [sp, #184]
  str x29, [sp, #176]
  add x29, sp, #176

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
  mov x0, #128
  str x0, [sp, #8]
.L5:
  mov x0, #7
  str x0, [sp, #16]
.L6:
  mov x0, #0
  str x0, [sp, #24]
.L7:
  ldr x1, [sp, #24]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L21
.L8:
  mov x0, #3
  str x0, [sp, #40]
.L9:
  ldr x1, [sp, #24]
  ldr x2, [sp, #40]
  mul x0, x1, x2
  str x0, [sp, #48]
.L10:
  mov x0, #1
  str x0, [sp, #56]
.L11:
  ldr x1, [sp, #48]
  ldr x2, [sp, #56]
  add x0, x1, x2
  str x0, [sp, #64]
.L12:
  ldr x1, [sp, #24]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #64]
  adrp x8, _arr_X@PAGE
  add x8, x8, _arr_X@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L13:
  mov x0, #2
  str x0, [sp, #72]
.L14:
  ldr x1, [sp, #24]
  ldr x2, [sp, #72]
  mul x0, x1, x2
  str x0, [sp, #80]
.L15:
  mov x0, #5
  str x0, [sp, #88]
.L16:
  ldr x1, [sp, #80]
  ldr x2, [sp, #88]
  add x0, x1, x2
  str x0, [sp, #96]
.L17:
  ldr x1, [sp, #24]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #96]
  adrp x8, _arr_Y@PAGE
  add x8, x8, _arr_Y@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L18:
  mov x0, #1
  str x0, [sp, #104]
.L19:
  ldr x1, [sp, #24]
  ldr x2, [sp, #104]
  add x0, x1, x2
  str x0, [sp, #24]
.L20:
  b .L7
.L21:
  mov x0, #0
  str x0, [sp, #24]
.L22:
  ldr x1, [sp, #24]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L31
.L23:
  ldr x1, [sp, #24]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_X@PAGE
  add x8, x8, _arr_X@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #112]
.L24:
  ldr x1, [sp, #16]
  ldr x2, [sp, #112]
  mul x0, x1, x2
  str x0, [sp, #120]
.L25:
  ldr x1, [sp, #24]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_Y@PAGE
  add x8, x8, _arr_Y@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #128]
.L26:
  ldr x1, [sp, #120]
  ldr x2, [sp, #128]
  add x0, x1, x2
  str x0, [sp, #136]
.L27:
  ldr x1, [sp, #24]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #136]
  adrp x8, _arr_Y@PAGE
  add x8, x8, _arr_Y@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L28:
  mov x0, #1
  str x0, [sp, #144]
.L29:
  ldr x1, [sp, #24]
  ldr x2, [sp, #144]
  add x0, x1, x2
  str x0, [sp, #24]
.L30:
  b .L22
.L31:
  mov x0, #0
  str x0, [sp, #32]
.L32:
  mov x0, #0
  str x0, [sp, #24]
.L33:
  ldr x1, [sp, #24]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L39
.L34:
  ldr x1, [sp, #24]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_Y@PAGE
  add x8, x8, _arr_Y@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #152]
.L35:
  ldr x1, [sp, #32]
  ldr x2, [sp, #152]
  add x0, x1, x2
  str x0, [sp, #32]
.L36:
  mov x0, #1
  str x0, [sp, #160]
.L37:
  ldr x1, [sp, #24]
  ldr x2, [sp, #160]
  add x0, x1, x2
  str x0, [sp, #24]
.L38:
  b .L33
.L39:
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
  // print i
  ldr x9, [sp, #24]
  sub sp, sp, #16
  adrp x8, .Lname_i@PAGE
  add x8, x8, .Lname_i@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print checksum
  ldr x9, [sp, #32]
  sub sp, sp, #16
  adrp x8, .Lname_checksum@PAGE
  add x8, x8, .Lname_checksum@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16

  // Exit with code 0
  mov x0, #0
  ldr x29, [sp, #176]
  ldr x30, [sp, #184]
  add sp, sp, #192
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
.Lname_a:
  .asciz "a"
.Lname_i:
  .asciz "i"
.Lname_checksum:
  .asciz "checksum"

.section __DATA,__data
.global _arr_X
.align 3
_arr_X:
  .space 8192
.global _arr_Y
.align 3
_arr_Y:
  .space 8192
