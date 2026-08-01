.global _main
.align 2

_main:
  sub sp, sp, #320
  str x30, [sp, #312]
  str x29, [sp, #304]
  add x29, sp, #304

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
  mov x0, #8
  str x0, [sp, #8]
.L7:
  mov x0, #0
  str x0, [sp, #16]
.L8:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L32
.L9:
  mov x0, #0
  str x0, [sp, #24]
.L10:
  ldr x1, [sp, #24]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L29
.L11:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  mul x0, x1, x2
  str x0, [sp, #56]
.L12:
  ldr x1, [sp, #56]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #64]
.L13:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  mul x0, x1, x2
  str x0, [sp, #72]
.L14:
  ldr x1, [sp, #72]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #80]
.L15:
  mov x0, #1
  str x0, [sp, #88]
.L16:
  ldr x1, [sp, #80]
  ldr x2, [sp, #88]
  add x0, x1, x2
  str x0, [sp, #96]
.L17:
  ldr x1, [sp, #64]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #96]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L18:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  mul x0, x1, x2
  str x0, [sp, #104]
.L19:
  ldr x1, [sp, #104]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #112]
.L20:
  ldr x1, [sp, #16]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #120]
.L21:
  mov x0, #7
  str x0, [sp, #128]
.L22:
  ldr x2, [sp, #128]
  cbz x2, .Ldiv_by_zero
  ldr x1, [sp, #120]
  ldr x2, [sp, #128]
  sdiv x3, x1, x2
  msub x0, x3, x2, x1
  str x0, [sp, #136]
.L23:
  mov x0, #1
  str x0, [sp, #144]
.L24:
  ldr x1, [sp, #136]
  ldr x2, [sp, #144]
  add x0, x1, x2
  str x0, [sp, #152]
.L25:
  ldr x1, [sp, #112]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #152]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L26:
  mov x0, #1
  str x0, [sp, #160]
.L27:
  ldr x1, [sp, #24]
  ldr x2, [sp, #160]
  add x0, x1, x2
  str x0, [sp, #24]
.L28:
  b .L10
.L29:
  mov x0, #1
  str x0, [sp, #168]
.L30:
  ldr x1, [sp, #16]
  ldr x2, [sp, #168]
  add x0, x1, x2
  str x0, [sp, #16]
.L31:
  b .L8
.L32:
  mov x0, #0
  str x0, [sp, #16]
.L33:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L59
.L34:
  mov x0, #0
  str x0, [sp, #24]
.L35:
  ldr x1, [sp, #24]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L56
.L36:
  mov x0, #0
  str x0, [sp, #40]
.L37:
  mov x0, #0
  str x0, [sp, #32]
.L38:
  ldr x1, [sp, #32]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L50
.L39:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  mul x0, x1, x2
  str x0, [sp, #176]
.L40:
  ldr x1, [sp, #176]
  ldr x2, [sp, #32]
  add x0, x1, x2
  str x0, [sp, #184]
.L41:
  ldr x1, [sp, #184]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #192]
.L42:
  ldr x1, [sp, #32]
  ldr x2, [sp, #8]
  mul x0, x1, x2
  str x0, [sp, #200]
.L43:
  ldr x1, [sp, #200]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #208]
.L44:
  ldr x1, [sp, #208]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #216]
.L45:
  ldr x1, [sp, #192]
  ldr x2, [sp, #216]
  mul x0, x1, x2
  str x0, [sp, #224]
.L46:
  ldr x1, [sp, #40]
  ldr x2, [sp, #224]
  add x0, x1, x2
  str x0, [sp, #40]
.L47:
  mov x0, #1
  str x0, [sp, #232]
.L48:
  ldr x1, [sp, #32]
  ldr x2, [sp, #232]
  add x0, x1, x2
  str x0, [sp, #32]
.L49:
  b .L38
.L50:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  mul x0, x1, x2
  str x0, [sp, #240]
.L51:
  ldr x1, [sp, #240]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #248]
.L52:
  ldr x1, [sp, #248]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #40]
  adrp x8, _arr_C@PAGE
  add x8, x8, _arr_C@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L53:
  mov x0, #1
  str x0, [sp, #256]
.L54:
  ldr x1, [sp, #24]
  ldr x2, [sp, #256]
  add x0, x1, x2
  str x0, [sp, #24]
.L55:
  b .L35
.L56:
  mov x0, #1
  str x0, [sp, #264]
.L57:
  ldr x1, [sp, #16]
  ldr x2, [sp, #264]
  add x0, x1, x2
  str x0, [sp, #16]
.L58:
  b .L33
.L59:
  mov x0, #0
  str x0, [sp, #48]
.L60:
  mov x0, #0
  str x0, [sp, #16]
.L61:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L69
.L62:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  mul x0, x1, x2
  str x0, [sp, #272]
.L63:
  ldr x1, [sp, #272]
  ldr x2, [sp, #16]
  add x0, x1, x2
  str x0, [sp, #280]
.L64:
  ldr x1, [sp, #280]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_C@PAGE
  add x8, x8, _arr_C@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #288]
.L65:
  ldr x1, [sp, #48]
  ldr x2, [sp, #288]
  add x0, x1, x2
  str x0, [sp, #48]
.L66:
  mov x0, #1
  str x0, [sp, #296]
.L67:
  ldr x1, [sp, #16]
  ldr x2, [sp, #296]
  add x0, x1, x2
  str x0, [sp, #16]
.L68:
  b .L61
.L69:
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
  // print k
  ldr x9, [sp, #32]
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
  ldr x9, [sp, #40]
  sub sp, sp, #16
  adrp x8, .Lname_s@PAGE
  add x8, x8, .Lname_s@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print trace
  ldr x9, [sp, #48]
  sub sp, sp, #16
  adrp x8, .Lname_trace@PAGE
  add x8, x8, .Lname_trace@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16

  // Exit with code 0
  mov x0, #0
  ldr x29, [sp, #304]
  ldr x30, [sp, #312]
  add sp, sp, #320
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
.Lname_k:
  .asciz "k"
.Lname_s:
  .asciz "s"
.Lname_trace:
  .asciz "trace"

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
