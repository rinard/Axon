.global _main
.align 2

_main:
  sub sp, sp, #496
  str x30, [sp, #488]
  str x29, [sp, #480]
  add x29, sp, #480

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
  str x0, [sp, #448]
  str x0, [sp, #456]
  str x0, [sp, #464]

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
  mov x0, #42
  str x0, [sp, #40]
.L9:
  mov x0, #3
  str x0, [sp, #48]
.L10:
  mov x0, #5
  str x0, [sp, #16]
.L11:
  mov x0, #0
  str x0, [sp, #72]
.L12:
  mov x0, #42
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
  mov x0, #0
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
  mov x0, #2
  str x0, [sp, #104]
.L18:
  mov x0, #10
  str x0, [sp, #112]
.L19:
  ldr x1, [sp, #104]
  cmp x1, #32
  b.hs .Lbounds_err
  ldr x2, [sp, #112]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L20:
  mov x0, #3
  str x0, [sp, #120]
.L21:
  mov x0, #7
  str x0, [sp, #128]
.L22:
  ldr x1, [sp, #120]
  cmp x1, #32
  b.hs .Lbounds_err
  ldr x2, [sp, #128]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L23:
  mov x0, #0
  str x0, [sp, #136]
.L24:
  mov x0, #2
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
  mov x0, #1
  str x0, [sp, #152]
.L27:
  mov x0, #42
  str x0, [sp, #160]
.L28:
  ldr x1, [sp, #152]
  cmp x1, #32
  b.hs .Lbounds_err
  ldr x2, [sp, #160]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L29:
  mov x0, #2
  str x0, [sp, #168]
.L30:
  mov x0, #2
  str x0, [sp, #176]
.L31:
  ldr x1, [sp, #168]
  cmp x1, #32
  b.hs .Lbounds_err
  ldr x2, [sp, #176]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L32:
  mov x0, #3
  str x0, [sp, #184]
.L33:
  mov x0, #0
  str x0, [sp, #192]
.L34:
  mov x0, #1
  str x0, [sp, #200]
.L35:
  ldr x1, [sp, #192]
  ldr x2, [sp, #200]
  sub x0, x1, x2
  str x0, [sp, #208]
.L36:
  ldr x1, [sp, #184]
  cmp x1, #32
  b.hs .Lbounds_err
  ldr x2, [sp, #208]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L37:
  mov x0, #32
  str x0, [sp, #216]
.L38:
  ldr x2, [sp, #216]
  cbz x2, .Ldiv_by_zero
  ldr x1, [sp, #48]
  ldr x2, [sp, #216]
  sdiv x3, x1, x2
  msub x0, x3, x2, x1
  str x0, [sp, #224]
.L39:
  mov x0, #32
  str x0, [sp, #232]
.L40:
  ldr x1, [sp, #224]
  ldr x2, [sp, #232]
  add x0, x1, x2
  str x0, [sp, #240]
.L41:
  mov x0, #32
  str x0, [sp, #248]
.L42:
  ldr x2, [sp, #248]
  cbz x2, .Ldiv_by_zero
  ldr x1, [sp, #240]
  ldr x2, [sp, #248]
  sdiv x3, x1, x2
  msub x0, x3, x2, x1
  str x0, [sp, #256]
.L43:
  mov x0, #0
  str x0, [sp, #264]
.L44:
  mov x0, #5
  str x0, [sp, #272]
.L45:
  ldr x1, [sp, #264]
  ldr x2, [sp, #272]
  sub x0, x1, x2
  str x0, [sp, #280]
.L46:
  ldr x1, [sp, #256]
  cmp x1, #32
  b.hs .Lbounds_err
  ldr x2, [sp, #280]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L47:
  mov x0, #16
  str x0, [sp, #288]
.L48:
  ldr x1, [sp, #288]
  cmp x1, #32
  b.hs .Lbounds_err
  ldr x2, [sp, #16]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L49:
  mov x0, #32
  str x0, [sp, #296]
.L50:
  ldr x2, [sp, #296]
  cbz x2, .Ldiv_by_zero
  ldr x1, [sp, #32]
  ldr x2, [sp, #296]
  sdiv x3, x1, x2
  msub x0, x3, x2, x1
  str x0, [sp, #304]
.L51:
  mov x0, #32
  str x0, [sp, #312]
.L52:
  ldr x1, [sp, #304]
  ldr x2, [sp, #312]
  add x0, x1, x2
  str x0, [sp, #320]
.L53:
  mov x0, #32
  str x0, [sp, #328]
.L54:
  ldr x2, [sp, #328]
  cbz x2, .Ldiv_by_zero
  ldr x1, [sp, #320]
  ldr x2, [sp, #328]
  sdiv x3, x1, x2
  msub x0, x3, x2, x1
  str x0, [sp, #336]
.L55:
  ldr x1, [sp, #336]
  cmp x1, #32
  b.hs .Lbounds_err
  ldr x2, [sp, #32]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L56:
  mov x0, #32
  str x0, [sp, #344]
.L57:
  ldr x2, [sp, #344]
  cbz x2, .Ldiv_by_zero
  ldr x1, [sp, #24]
  ldr x2, [sp, #344]
  sdiv x3, x1, x2
  msub x0, x3, x2, x1
  str x0, [sp, #352]
.L58:
  mov x0, #32
  str x0, [sp, #360]
.L59:
  ldr x1, [sp, #352]
  ldr x2, [sp, #360]
  add x0, x1, x2
  str x0, [sp, #368]
.L60:
  mov x0, #32
  str x0, [sp, #376]
.L61:
  ldr x2, [sp, #376]
  cbz x2, .Ldiv_by_zero
  ldr x1, [sp, #368]
  ldr x2, [sp, #376]
  sdiv x3, x1, x2
  msub x0, x3, x2, x1
  str x0, [sp, #384]
.L62:
  ldr x1, [sp, #384]
  cmp x1, #32
  b.hs .Lbounds_err
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #392]
.L63:
  ldr x0, [sp, #392]
  str x0, [sp, #8]
.L64:
  mov x0, #0
  str x0, [sp, #400]
.L65:
  mov x0, #0
  str x0, [sp, #408]
.L66:
  ldr x1, [sp, #408]
  ldr x2, [sp, #16]
  add x0, x1, x2
  str x0, [sp, #416]
.L67:
  ldr x1, [sp, #400]
  ldr x2, [sp, #416]
  mul x0, x1, x2
  str x0, [sp, #8]
.L68:
  mov x0, #0
  str x0, [sp, #424]
.L69:
  mov x0, #1
  str x0, [sp, #432]
.L70:
  ldr x1, [sp, #424]
  ldr x2, [sp, #432]
  sub x0, x1, x2
  str x0, [sp, #440]
.L71:
  mov x0, #5
  str x0, [sp, #448]
.L72:
  ldr x1, [sp, #440]
  ldr x2, [sp, #448]
  cmp x1, x2
  cset w0, le
  eor w0, w0, #1
  cbnz w0, .L75
.L73:
  ldr x0, [sp, #56]
  str x0, [sp, #56]
.L74:
  b .L81
.L75:
  mov x0, #5
  str x0, [sp, #456]
.L76:
  ldr x1, [sp, #16]
  ldr x2, [sp, #456]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L81
.L77:
  ldr x0, [sp, #40]
  str x0, [sp, #8]
.L78:
  mov x0, #1
  str x0, [sp, #464]
.L79:
  ldr x1, [sp, #16]
  ldr x2, [sp, #464]
  add x0, x1, x2
  str x0, [sp, #16]
.L80:
  b .L75
.L81:
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
  ldr x29, [sp, #480]
  ldr x30, [sp, #488]
  add sp, sp, #496
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
