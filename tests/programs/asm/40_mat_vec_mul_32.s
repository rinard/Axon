.global _main
.align 2

_main:
  sub sp, sp, #224
  str x30, [sp, #216]
  str x29, [sp, #208]
  add x29, sp, #208

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
  mov x0, #32
  str x0, [sp, #8]
.L6:
  mov x0, #0
  str x0, [sp, #16]
.L7:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L27
.L8:
  mov x0, #1
  str x0, [sp, #48]
.L9:
  ldr x1, [sp, #16]
  ldr x2, [sp, #48]
  add x0, x1, x2
  str x0, [sp, #56]
.L10:
  ldr x1, [sp, #16]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #56]
  adrp x8, _arr_X@PAGE
  add x8, x8, _arr_X@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L11:
  mov x0, #0
  str x0, [sp, #24]
.L12:
  ldr x1, [sp, #24]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L24
.L13:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  mul x0, x1, x2
  str x0, [sp, #64]
.L14:
  ldr x1, [sp, #64]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #72]
.L15:
  ldr x1, [sp, #16]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #80]
.L16:
  mov x0, #10
  str x0, [sp, #88]
.L17:
  ldr x2, [sp, #88]
  cbz x2, .Ldiv_by_zero
  ldr x1, [sp, #80]
  ldr x2, [sp, #88]
  sdiv x3, x1, x2
  msub x0, x3, x2, x1
  str x0, [sp, #96]
.L18:
  mov x0, #1
  str x0, [sp, #104]
.L19:
  ldr x1, [sp, #96]
  ldr x2, [sp, #104]
  add x0, x1, x2
  str x0, [sp, #112]
.L20:
  ldr x1, [sp, #72]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #112]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L21:
  mov x0, #1
  str x0, [sp, #120]
.L22:
  ldr x1, [sp, #24]
  ldr x2, [sp, #120]
  add x0, x1, x2
  str x0, [sp, #24]
.L23:
  b .L12
.L24:
  mov x0, #1
  str x0, [sp, #128]
.L25:
  ldr x1, [sp, #16]
  ldr x2, [sp, #128]
  add x0, x1, x2
  str x0, [sp, #16]
.L26:
  b .L7
.L27:
  mov x0, #0
  str x0, [sp, #16]
.L28:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L45
.L29:
  mov x0, #0
  str x0, [sp, #32]
.L30:
  mov x0, #0
  str x0, [sp, #24]
.L31:
  ldr x1, [sp, #24]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L41
.L32:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  mul x0, x1, x2
  str x0, [sp, #136]
.L33:
  ldr x1, [sp, #136]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #144]
.L34:
  ldr x1, [sp, #144]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #152]
.L35:
  ldr x1, [sp, #24]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_X@PAGE
  add x8, x8, _arr_X@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #160]
.L36:
  ldr x1, [sp, #152]
  ldr x2, [sp, #160]
  mul x0, x1, x2
  str x0, [sp, #168]
.L37:
  ldr x1, [sp, #32]
  ldr x2, [sp, #168]
  add x0, x1, x2
  str x0, [sp, #32]
.L38:
  mov x0, #1
  str x0, [sp, #176]
.L39:
  ldr x1, [sp, #24]
  ldr x2, [sp, #176]
  add x0, x1, x2
  str x0, [sp, #24]
.L40:
  b .L31
.L41:
  ldr x1, [sp, #16]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #32]
  adrp x8, _arr_Y@PAGE
  add x8, x8, _arr_Y@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L42:
  mov x0, #1
  str x0, [sp, #184]
.L43:
  ldr x1, [sp, #16]
  ldr x2, [sp, #184]
  add x0, x1, x2
  str x0, [sp, #16]
.L44:
  b .L28
.L45:
  mov x0, #0
  str x0, [sp, #40]
.L46:
  mov x0, #0
  str x0, [sp, #16]
.L47:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L53
.L48:
  ldr x1, [sp, #16]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_Y@PAGE
  add x8, x8, _arr_Y@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #192]
.L49:
  ldr x1, [sp, #40]
  ldr x2, [sp, #192]
  add x0, x1, x2
  str x0, [sp, #40]
.L50:
  mov x0, #1
  str x0, [sp, #200]
.L51:
  ldr x1, [sp, #16]
  ldr x2, [sp, #200]
  add x0, x1, x2
  str x0, [sp, #16]
.L52:
  b .L47
.L53:
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
  // print k
  ldr x9, [sp, #24]
  sub sp, sp, #16
  adrp x8, .Lname_k@PAGE
  add x8, x8, .Lname_k@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print s
  ldr x9, [sp, #32]
  sub sp, sp, #16
  adrp x8, .Lname_s@PAGE
  add x8, x8, .Lname_s@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print checksum
  ldr x9, [sp, #40]
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
  ldr x29, [sp, #208]
  ldr x30, [sp, #216]
  add sp, sp, #224
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
.Lname_k:
  .asciz "k"
.Lname_s:
  .asciz "s"
.Lname_checksum:
  .asciz "checksum"

.section __DATA,__data
.global _arr_X
.align 3
_arr_X:
  .space 8192
.global _arr_A
.align 3
_arr_A:
  .space 8192
.global _arr_Y
.align 3
_arr_Y:
  .space 8192
