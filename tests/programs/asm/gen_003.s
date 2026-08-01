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
  mov x0, #3
  str x0, [sp, #8]
.L9:
  mov x0, #100
  str x0, [sp, #16]
.L10:
  mov x0, #42
  str x0, [sp, #40]
.L11:
  mov x0, #0
  str x0, [sp, #72]
.L12:
  mov x0, #10
  str x0, [sp, #80]
.L13:
  ldr x1, [sp, #72]
  cmp x1, #32
  b.hs .Lbounds_err
  ldr x2, [sp, #80]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L14:
  mov x0, #1
  str x0, [sp, #88]
.L15:
  mov x0, #2
  str x0, [sp, #96]
.L16:
  ldr x1, [sp, #88]
  cmp x1, #32
  b.hs .Lbounds_err
  ldr x2, [sp, #96]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L17:
  mov x0, #0
  str x0, [sp, #104]
.L18:
  mov x0, #42
  str x0, [sp, #112]
.L19:
  ldr x1, [sp, #104]
  cmp x1, #32
  b.hs .Lbounds_err
  ldr x2, [sp, #112]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L20:
  mov x0, #1
  str x0, [sp, #120]
.L21:
  mov x0, #3
  str x0, [sp, #128]
.L22:
  ldr x1, [sp, #120]
  cmp x1, #32
  b.hs .Lbounds_err
  ldr x2, [sp, #128]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L23:
  mov x0, #2
  str x0, [sp, #136]
.L24:
  mov x0, #1
  str x0, [sp, #144]
.L25:
  ldr x1, [sp, #136]
  cmp x1, #32
  b.hs .Lbounds_err
  ldr x2, [sp, #144]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L26:
  mov x0, #0
  str x0, [sp, #152]
.L27:
  mov x0, #32
  str x0, [sp, #160]
.L28:
  ldr x2, [sp, #160]
  cbz x2, .Ldiv_by_zero
  ldr x1, [sp, #16]
  ldr x2, [sp, #160]
  sdiv x3, x1, x2
  msub x0, x3, x2, x1
  str x0, [sp, #168]
.L29:
  mov x0, #32
  str x0, [sp, #176]
.L30:
  ldr x1, [sp, #168]
  ldr x2, [sp, #176]
  add x0, x1, x2
  str x0, [sp, #184]
.L31:
  mov x0, #32
  str x0, [sp, #192]
.L32:
  ldr x2, [sp, #192]
  cbz x2, .Ldiv_by_zero
  ldr x1, [sp, #184]
  ldr x2, [sp, #192]
  sdiv x3, x1, x2
  msub x0, x3, x2, x1
  str x0, [sp, #200]
.L33:
  ldr x1, [sp, #200]
  cmp x1, #32
  b.hs .Lbounds_err
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #208]
.L34:
  ldr x1, [sp, #32]
  ldr x2, [sp, #208]
  add x0, x1, x2
  str x0, [sp, #216]
.L35:
  ldr x1, [sp, #152]
  cmp x1, #32
  b.hs .Lbounds_err
  ldr x2, [sp, #216]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L36:
  ldr x1, [sp, #48]
  ldr x2, [sp, #16]
  mul x0, x1, x2
  str x0, [sp, #224]
.L37:
  ldr x1, [sp, #48]
  ldr x2, [sp, #224]
  cmp x1, x2
  cset w0, ne
  str x0, [sp, #64]
.L38:
  mov x0, #100
  str x0, [sp, #232]
.L39:
  ldr x1, [sp, #40]
  ldr x2, [sp, #232]
  add x0, x1, x2
  str x0, [sp, #240]
.L40:
  mov x0, #1
  str x0, [sp, #248]
.L41:
  ldr x2, [sp, #248]
  cbz x2, .Ldiv_by_zero
  ldr x1, [sp, #240]
  ldr x2, [sp, #248]
  sdiv x0, x1, x2
  str x0, [sp, #8]
.L42:
  mov x0, #3
  str x0, [sp, #256]
.L43:
  ldr x1, [sp, #8]
  ldr x2, [sp, #256]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L52
.L44:
  mov x0, #10
  str x0, [sp, #264]
.L45:
  mov x0, #0
  str x0, [sp, #272]
.L46:
  mov x0, #1
  str x0, [sp, #280]
.L47:
  ldr x1, [sp, #272]
  ldr x2, [sp, #280]
  sub x0, x1, x2
  str x0, [sp, #288]
.L48:
  ldr x1, [sp, #264]
  ldr x2, [sp, #288]
  add x0, x1, x2
  str x0, [sp, #8]
.L49:
  mov x0, #1
  str x0, [sp, #296]
.L50:
  ldr x1, [sp, #8]
  ldr x2, [sp, #296]
  add x0, x1, x2
  str x0, [sp, #8]
.L51:
  b .L42
.L52:
  ldr x1, [sp, #24]
  ldr x2, [sp, #48]
  sub x0, x1, x2
  str x0, [sp, #304]
.L53:
  mov x0, #32
  str x0, [sp, #312]
.L54:
  ldr x2, [sp, #312]
  cbz x2, .Ldiv_by_zero
  ldr x1, [sp, #16]
  ldr x2, [sp, #312]
  sdiv x3, x1, x2
  msub x0, x3, x2, x1
  str x0, [sp, #320]
.L55:
  mov x0, #32
  str x0, [sp, #328]
.L56:
  ldr x1, [sp, #320]
  ldr x2, [sp, #328]
  add x0, x1, x2
  str x0, [sp, #336]
.L57:
  mov x0, #32
  str x0, [sp, #344]
.L58:
  ldr x2, [sp, #344]
  cbz x2, .Ldiv_by_zero
  ldr x1, [sp, #336]
  ldr x2, [sp, #344]
  sdiv x3, x1, x2
  msub x0, x3, x2, x1
  str x0, [sp, #352]
.L59:
  ldr x1, [sp, #352]
  cmp x1, #32
  b.hs .Lbounds_err
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #360]
.L60:
  ldr x1, [sp, #304]
  ldr x2, [sp, #360]
  cmp x1, x2
  cset w0, lt
  cbnz w0, .L70
.L61:
  mov x0, #32
  str x0, [sp, #368]
.L62:
  ldr x2, [sp, #368]
  cbz x2, .Ldiv_by_zero
  ldr x1, [sp, #8]
  ldr x2, [sp, #368]
  sdiv x3, x1, x2
  msub x0, x3, x2, x1
  str x0, [sp, #376]
.L63:
  mov x0, #32
  str x0, [sp, #384]
.L64:
  ldr x1, [sp, #376]
  ldr x2, [sp, #384]
  add x0, x1, x2
  str x0, [sp, #392]
.L65:
  mov x0, #32
  str x0, [sp, #400]
.L66:
  ldr x2, [sp, #400]
  cbz x2, .Ldiv_by_zero
  ldr x1, [sp, #392]
  ldr x2, [sp, #400]
  sdiv x3, x1, x2
  msub x0, x3, x2, x1
  str x0, [sp, #408]
.L67:
  ldr x1, [sp, #16]
  ldr x2, [sp, #48]
  sub x0, x1, x2
  str x0, [sp, #416]
.L68:
  ldr x1, [sp, #408]
  cmp x1, #32
  b.hs .Lbounds_err
  ldr x2, [sp, #416]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L69:
  b .L73
.L70:
  mov x0, #6
  str x0, [sp, #424]
.L71:
  mov x0, #3
  str x0, [sp, #432]
.L72:
  ldr x1, [sp, #424]
  cmp x1, #32
  b.hs .Lbounds_err
  ldr x2, [sp, #432]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L73:
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
