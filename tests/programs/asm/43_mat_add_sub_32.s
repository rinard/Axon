.global _main
.align 2

_main:
  sub sp, sp, #336
  str x30, [sp, #328]
  str x29, [sp, #320]
  add x29, sp, #320

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
  str x0, [sp, #248]
  str x0, [sp, #256]
  str x0, [sp, #264]
  str x0, [sp, #272]
  str x0, [sp, #280]
  str x0, [sp, #288]
  str x0, [sp, #296]
  str x0, [sp, #304]
  str x0, [sp, #312]

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
  cbnz w0, .L34
.L8:
  mov x0, #0
  str x0, [sp, #24]
.L9:
  ldr x1, [sp, #24]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L31
.L10:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  mul x0, x1, x2
  str x0, [sp, #48]
.L11:
  ldr x1, [sp, #48]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #32]
.L12:
  mov x0, #5
  str x0, [sp, #56]
.L13:
  ldr x1, [sp, #16]
  ldr x2, [sp, #56]
  mul x0, x1, x2
  str x0, [sp, #64]
.L14:
  mov x0, #3
  str x0, [sp, #72]
.L15:
  ldr x1, [sp, #24]
  ldr x2, [sp, #72]
  mul x0, x1, x2
  str x0, [sp, #80]
.L16:
  ldr x1, [sp, #64]
  ldr x2, [sp, #80]
  add x0, x1, x2
  str x0, [sp, #88]
.L17:
  mov x0, #1
  str x0, [sp, #96]
.L18:
  ldr x1, [sp, #88]
  ldr x2, [sp, #96]
  add x0, x1, x2
  str x0, [sp, #104]
.L19:
  ldr x1, [sp, #32]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #104]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L20:
  mov x0, #2
  str x0, [sp, #112]
.L21:
  ldr x1, [sp, #16]
  ldr x2, [sp, #112]
  mul x0, x1, x2
  str x0, [sp, #120]
.L22:
  mov x0, #7
  str x0, [sp, #128]
.L23:
  ldr x1, [sp, #24]
  ldr x2, [sp, #128]
  mul x0, x1, x2
  str x0, [sp, #136]
.L24:
  ldr x1, [sp, #120]
  ldr x2, [sp, #136]
  add x0, x1, x2
  str x0, [sp, #144]
.L25:
  mov x0, #4
  str x0, [sp, #152]
.L26:
  ldr x1, [sp, #144]
  ldr x2, [sp, #152]
  add x0, x1, x2
  str x0, [sp, #160]
.L27:
  ldr x1, [sp, #32]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #160]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L28:
  mov x0, #1
  str x0, [sp, #168]
.L29:
  ldr x1, [sp, #24]
  ldr x2, [sp, #168]
  add x0, x1, x2
  str x0, [sp, #24]
.L30:
  b .L9
.L31:
  mov x0, #1
  str x0, [sp, #176]
.L32:
  ldr x1, [sp, #16]
  ldr x2, [sp, #176]
  add x0, x1, x2
  str x0, [sp, #16]
.L33:
  b .L7
.L34:
  mov x0, #0
  str x0, [sp, #16]
.L35:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L50
.L36:
  mov x0, #0
  str x0, [sp, #24]
.L37:
  ldr x1, [sp, #24]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L47
.L38:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  mul x0, x1, x2
  str x0, [sp, #184]
.L39:
  ldr x1, [sp, #184]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #32]
.L40:
  ldr x1, [sp, #32]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #192]
.L41:
  ldr x1, [sp, #32]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #200]
.L42:
  ldr x1, [sp, #192]
  ldr x2, [sp, #200]
  add x0, x1, x2
  str x0, [sp, #208]
.L43:
  ldr x1, [sp, #32]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #208]
  adrp x8, _arr_C@PAGE
  add x8, x8, _arr_C@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L44:
  mov x0, #1
  str x0, [sp, #216]
.L45:
  ldr x1, [sp, #24]
  ldr x2, [sp, #216]
  add x0, x1, x2
  str x0, [sp, #24]
.L46:
  b .L37
.L47:
  mov x0, #1
  str x0, [sp, #224]
.L48:
  ldr x1, [sp, #16]
  ldr x2, [sp, #224]
  add x0, x1, x2
  str x0, [sp, #16]
.L49:
  b .L35
.L50:
  mov x0, #0
  str x0, [sp, #16]
.L51:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L66
.L52:
  mov x0, #0
  str x0, [sp, #24]
.L53:
  ldr x1, [sp, #24]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L63
.L54:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  mul x0, x1, x2
  str x0, [sp, #232]
.L55:
  ldr x1, [sp, #232]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #32]
.L56:
  ldr x1, [sp, #32]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_C@PAGE
  add x8, x8, _arr_C@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #240]
.L57:
  ldr x1, [sp, #32]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #248]
.L58:
  ldr x1, [sp, #240]
  ldr x2, [sp, #248]
  sub x0, x1, x2
  str x0, [sp, #256]
.L59:
  ldr x1, [sp, #32]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #256]
  adrp x8, _arr_C@PAGE
  add x8, x8, _arr_C@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L60:
  mov x0, #1
  str x0, [sp, #264]
.L61:
  ldr x1, [sp, #24]
  ldr x2, [sp, #264]
  add x0, x1, x2
  str x0, [sp, #24]
.L62:
  b .L53
.L63:
  mov x0, #1
  str x0, [sp, #272]
.L64:
  ldr x1, [sp, #16]
  ldr x2, [sp, #272]
  add x0, x1, x2
  str x0, [sp, #16]
.L65:
  b .L51
.L66:
  mov x0, #0
  str x0, [sp, #40]
.L67:
  mov x0, #0
  str x0, [sp, #16]
.L68:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L81
.L69:
  mov x0, #0
  str x0, [sp, #24]
.L70:
  ldr x1, [sp, #24]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L78
.L71:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  mul x0, x1, x2
  str x0, [sp, #280]
.L72:
  ldr x1, [sp, #280]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #288]
.L73:
  ldr x1, [sp, #288]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_C@PAGE
  add x8, x8, _arr_C@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #296]
.L74:
  ldr x1, [sp, #40]
  ldr x2, [sp, #296]
  add x0, x1, x2
  str x0, [sp, #40]
.L75:
  mov x0, #1
  str x0, [sp, #304]
.L76:
  ldr x1, [sp, #24]
  ldr x2, [sp, #304]
  add x0, x1, x2
  str x0, [sp, #24]
.L77:
  b .L70
.L78:
  mov x0, #1
  str x0, [sp, #312]
.L79:
  ldr x1, [sp, #16]
  ldr x2, [sp, #312]
  add x0, x1, x2
  str x0, [sp, #16]
.L80:
  b .L68
.L81:
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
  // print idx
  ldr x9, [sp, #32]
  sub sp, sp, #16
  adrp x8, .Lname_idx@PAGE
  add x8, x8, .Lname_idx@PAGEOFF
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
  ldr x29, [sp, #320]
  ldr x30, [sp, #328]
  add sp, sp, #336
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
.Lname_idx:
  .asciz "idx"
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
.global _arr_C
.align 3
_arr_C:
  .space 8192
