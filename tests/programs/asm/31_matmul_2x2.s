.global _main
.align 2

_main:
  sub sp, sp, #464
  str x30, [sp, #456]
  str x29, [sp, #448]
  add x29, sp, #448

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
  str x0, [sp, #320]
  str x0, [sp, #328]
  str x0, [sp, #336]
  str x0, [sp, #344]
  str x0, [sp, #352]
  str x0, [sp, #360]
  str x0, [sp, #368]
  str x0, [sp, #376]
  str x0, [sp, #384]
  str x0, [sp, #392]
  str x0, [sp, #400]
  str x0, [sp, #408]
  str x0, [sp, #416]
  str x0, [sp, #424]
  str x0, [sp, #432]
  str x0, [sp, #440]

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
  mov x0, #1
  str x0, [sp, #56]
.L7:
  ldr x1, [sp, #48]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #56]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L8:
  mov x0, #1
  str x0, [sp, #64]
.L9:
  mov x0, #2
  str x0, [sp, #72]
.L10:
  ldr x1, [sp, #64]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #72]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L11:
  mov x0, #2
  str x0, [sp, #80]
.L12:
  mov x0, #3
  str x0, [sp, #88]
.L13:
  ldr x1, [sp, #80]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #88]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L14:
  mov x0, #3
  str x0, [sp, #96]
.L15:
  mov x0, #4
  str x0, [sp, #104]
.L16:
  ldr x1, [sp, #96]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #104]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L17:
  mov x0, #0
  str x0, [sp, #112]
.L18:
  mov x0, #5
  str x0, [sp, #120]
.L19:
  ldr x1, [sp, #112]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #120]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L20:
  mov x0, #1
  str x0, [sp, #128]
.L21:
  mov x0, #6
  str x0, [sp, #136]
.L22:
  ldr x1, [sp, #128]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #136]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L23:
  mov x0, #2
  str x0, [sp, #144]
.L24:
  mov x0, #7
  str x0, [sp, #152]
.L25:
  ldr x1, [sp, #144]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #152]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L26:
  mov x0, #3
  str x0, [sp, #160]
.L27:
  mov x0, #8
  str x0, [sp, #168]
.L28:
  ldr x1, [sp, #160]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #168]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L29:
  mov x0, #0
  str x0, [sp, #8]
.L30:
  mov x0, #2
  str x0, [sp, #176]
.L31:
  ldr x1, [sp, #8]
  ldr x2, [sp, #176]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L62
.L32:
  mov x0, #0
  str x0, [sp, #16]
.L33:
  mov x0, #2
  str x0, [sp, #184]
.L34:
  ldr x1, [sp, #16]
  ldr x2, [sp, #184]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L59
.L35:
  mov x0, #0
  str x0, [sp, #32]
.L36:
  mov x0, #0
  str x0, [sp, #24]
.L37:
  mov x0, #2
  str x0, [sp, #192]
.L38:
  ldr x1, [sp, #24]
  ldr x2, [sp, #192]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L52
.L39:
  mov x0, #2
  str x0, [sp, #200]
.L40:
  ldr x1, [sp, #8]
  ldr x2, [sp, #200]
  mul x0, x1, x2
  str x0, [sp, #208]
.L41:
  ldr x1, [sp, #208]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #216]
.L42:
  ldr x1, [sp, #216]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #224]
.L43:
  mov x0, #2
  str x0, [sp, #232]
.L44:
  ldr x1, [sp, #24]
  ldr x2, [sp, #232]
  mul x0, x1, x2
  str x0, [sp, #240]
.L45:
  ldr x1, [sp, #240]
  ldr x2, [sp, #16]
  add x0, x1, x2
  str x0, [sp, #248]
.L46:
  ldr x1, [sp, #248]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #256]
.L47:
  ldr x1, [sp, #224]
  ldr x2, [sp, #256]
  mul x0, x1, x2
  str x0, [sp, #264]
.L48:
  ldr x1, [sp, #32]
  ldr x2, [sp, #264]
  add x0, x1, x2
  str x0, [sp, #32]
.L49:
  mov x0, #1
  str x0, [sp, #272]
.L50:
  ldr x1, [sp, #24]
  ldr x2, [sp, #272]
  add x0, x1, x2
  str x0, [sp, #24]
.L51:
  b .L37
.L52:
  mov x0, #2
  str x0, [sp, #280]
.L53:
  ldr x1, [sp, #8]
  ldr x2, [sp, #280]
  mul x0, x1, x2
  str x0, [sp, #288]
.L54:
  ldr x1, [sp, #288]
  ldr x2, [sp, #16]
  add x0, x1, x2
  str x0, [sp, #296]
.L55:
  ldr x1, [sp, #296]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #32]
  adrp x8, _arr_C@PAGE
  add x8, x8, _arr_C@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L56:
  mov x0, #1
  str x0, [sp, #304]
.L57:
  ldr x1, [sp, #16]
  ldr x2, [sp, #304]
  add x0, x1, x2
  str x0, [sp, #16]
.L58:
  b .L33
.L59:
  mov x0, #1
  str x0, [sp, #312]
.L60:
  ldr x1, [sp, #8]
  ldr x2, [sp, #312]
  add x0, x1, x2
  str x0, [sp, #8]
.L61:
  b .L30
.L62:
  mov x0, #0
  str x0, [sp, #320]
.L63:
  ldr x1, [sp, #320]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_C@PAGE
  add x8, x8, _arr_C@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #328]
.L64:
  movz x0, #16960
  movk x0, #15, lsl #16
  str x0, [sp, #336]
.L65:
  ldr x1, [sp, #328]
  ldr x2, [sp, #336]
  mul x0, x1, x2
  str x0, [sp, #344]
.L66:
  mov x0, #1
  str x0, [sp, #352]
.L67:
  ldr x1, [sp, #352]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_C@PAGE
  add x8, x8, _arr_C@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #360]
.L68:
  mov x0, #10000
  str x0, [sp, #368]
.L69:
  ldr x1, [sp, #360]
  ldr x2, [sp, #368]
  mul x0, x1, x2
  str x0, [sp, #376]
.L70:
  ldr x1, [sp, #344]
  ldr x2, [sp, #376]
  add x0, x1, x2
  str x0, [sp, #384]
.L71:
  mov x0, #2
  str x0, [sp, #392]
.L72:
  ldr x1, [sp, #392]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_C@PAGE
  add x8, x8, _arr_C@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #400]
.L73:
  mov x0, #100
  str x0, [sp, #408]
.L74:
  ldr x1, [sp, #400]
  ldr x2, [sp, #408]
  mul x0, x1, x2
  str x0, [sp, #416]
.L75:
  ldr x1, [sp, #384]
  ldr x2, [sp, #416]
  add x0, x1, x2
  str x0, [sp, #424]
.L76:
  mov x0, #3
  str x0, [sp, #432]
.L77:
  ldr x1, [sp, #432]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_C@PAGE
  add x8, x8, _arr_C@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #440]
.L78:
  ldr x1, [sp, #424]
  ldr x2, [sp, #440]
  add x0, x1, x2
  str x0, [sp, #40]
.L79:
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
  // print j
  ldr x9, [sp, #16]
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
  // print r
  ldr x9, [sp, #40]
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
  ldr x29, [sp, #448]
  ldr x30, [sp, #456]
  add sp, sp, #464
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
.Lname_j:
  .asciz "j"
.Lname_k:
  .asciz "k"
.Lname_s:
  .asciz "s"
.Lname_r:
  .asciz "r"

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
