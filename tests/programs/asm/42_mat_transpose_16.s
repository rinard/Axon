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
  mov x0, #0
  str x0, [sp, #32]
.L4:
  mov x0, #16
  str x0, [sp, #8]
.L5:
  mov x0, #0
  str x0, [sp, #16]
.L6:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L21
.L7:
  mov x0, #0
  str x0, [sp, #24]
.L8:
  ldr x1, [sp, #24]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L18
.L9:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  mul x0, x1, x2
  str x0, [sp, #40]
.L10:
  ldr x1, [sp, #40]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #48]
.L11:
  mov x0, #100
  str x0, [sp, #56]
.L12:
  ldr x1, [sp, #16]
  ldr x2, [sp, #56]
  mul x0, x1, x2
  str x0, [sp, #64]
.L13:
  ldr x1, [sp, #64]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #72]
.L14:
  ldr x1, [sp, #48]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #72]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L15:
  mov x0, #1
  str x0, [sp, #80]
.L16:
  ldr x1, [sp, #24]
  ldr x2, [sp, #80]
  add x0, x1, x2
  str x0, [sp, #24]
.L17:
  b .L8
.L18:
  mov x0, #1
  str x0, [sp, #88]
.L19:
  ldr x1, [sp, #16]
  ldr x2, [sp, #88]
  add x0, x1, x2
  str x0, [sp, #16]
.L20:
  b .L6
.L21:
  mov x0, #0
  str x0, [sp, #16]
.L22:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L37
.L23:
  mov x0, #0
  str x0, [sp, #24]
.L24:
  ldr x1, [sp, #24]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L34
.L25:
  ldr x1, [sp, #24]
  ldr x2, [sp, #8]
  mul x0, x1, x2
  str x0, [sp, #96]
.L26:
  ldr x1, [sp, #96]
  ldr x2, [sp, #16]
  add x0, x1, x2
  str x0, [sp, #104]
.L27:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  mul x0, x1, x2
  str x0, [sp, #112]
.L28:
  ldr x1, [sp, #112]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #120]
.L29:
  ldr x1, [sp, #120]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #128]
.L30:
  ldr x1, [sp, #104]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #128]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L31:
  mov x0, #1
  str x0, [sp, #136]
.L32:
  ldr x1, [sp, #24]
  ldr x2, [sp, #136]
  add x0, x1, x2
  str x0, [sp, #24]
.L33:
  b .L24
.L34:
  mov x0, #1
  str x0, [sp, #144]
.L35:
  ldr x1, [sp, #16]
  ldr x2, [sp, #144]
  add x0, x1, x2
  str x0, [sp, #16]
.L36:
  b .L22
.L37:
  mov x0, #0
  str x0, [sp, #32]
.L38:
  mov x0, #0
  str x0, [sp, #16]
.L39:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L52
.L40:
  mov x0, #0
  str x0, [sp, #24]
.L41:
  ldr x1, [sp, #24]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L49
.L42:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  mul x0, x1, x2
  str x0, [sp, #152]
.L43:
  ldr x1, [sp, #152]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #160]
.L44:
  ldr x1, [sp, #160]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #168]
.L45:
  ldr x1, [sp, #32]
  ldr x2, [sp, #168]
  add x0, x1, x2
  str x0, [sp, #32]
.L46:
  mov x0, #1
  str x0, [sp, #176]
.L47:
  ldr x1, [sp, #24]
  ldr x2, [sp, #176]
  add x0, x1, x2
  str x0, [sp, #24]
.L48:
  b .L41
.L49:
  mov x0, #1
  str x0, [sp, #184]
.L50:
  ldr x1, [sp, #16]
  ldr x2, [sp, #184]
  add x0, x1, x2
  str x0, [sp, #16]
.L51:
  b .L39
.L52:
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
  // print j
  ldr x9, [sp, #24]
  sub sp, sp, #16
  adrp x8, .Lname_j@PAGE
  add x8, x8, .Lname_j@PAGEOFF
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
.Lname_j:
  .asciz "j"
.Lname_checksum:
  .asciz "checksum"

.section __DATA,__data
.global _arr_A
.align 3
_arr_A:
  .space 8192
.global _arr_B
.align 3
_arr_B:
  .space 8192
