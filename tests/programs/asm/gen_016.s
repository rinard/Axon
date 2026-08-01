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
  str x0, [sp, #472]

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
  mov x0, #0
  str x0, [sp, #72]
.L9:
  mov x0, #1
  str x0, [sp, #80]
.L10:
  ldr x1, [sp, #72]
  ldr x2, [sp, #80]
  sub x0, x1, x2
  str x0, [sp, #8]
.L11:
  mov x0, #10
  str x0, [sp, #24]
.L12:
  mov x0, #0
  str x0, [sp, #88]
.L13:
  mov x0, #5
  str x0, [sp, #96]
.L14:
  ldr x1, [sp, #88]
  ldr x2, [sp, #96]
  sub x0, x1, x2
  str x0, [sp, #32]
.L15:
  mov x0, #0
  str x0, [sp, #104]
.L16:
  mov x0, #5
  str x0, [sp, #112]
.L17:
  ldr x1, [sp, #104]
  cmp x1, #32
  b.hs .Lbounds_err
  ldr x2, [sp, #112]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L18:
  mov x0, #1
  str x0, [sp, #120]
.L19:
  mov x0, #1
  str x0, [sp, #128]
.L20:
  ldr x1, [sp, #120]
  cmp x1, #32
  b.hs .Lbounds_err
  ldr x2, [sp, #128]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L21:
  mov x0, #2
  str x0, [sp, #136]
.L22:
  mov x0, #10
  str x0, [sp, #144]
.L23:
  ldr x1, [sp, #136]
  cmp x1, #32
  b.hs .Lbounds_err
  ldr x2, [sp, #144]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L24:
  mov x0, #3
  str x0, [sp, #152]
.L25:
  mov x0, #0
  str x0, [sp, #160]
.L26:
  ldr x1, [sp, #152]
  cmp x1, #32
  b.hs .Lbounds_err
  ldr x2, [sp, #160]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L27:
  mov x0, #0
  str x0, [sp, #168]
.L28:
  mov x0, #2
  str x0, [sp, #176]
.L29:
  ldr x1, [sp, #168]
  cmp x1, #32
  b.hs .Lbounds_err
  ldr x2, [sp, #176]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L30:
  mov x0, #1
  str x0, [sp, #184]
.L31:
  mov x0, #0
  str x0, [sp, #192]
.L32:
  mov x0, #1
  str x0, [sp, #200]
.L33:
  ldr x1, [sp, #192]
  ldr x2, [sp, #200]
  sub x0, x1, x2
  str x0, [sp, #208]
.L34:
  ldr x1, [sp, #184]
  cmp x1, #32
  b.hs .Lbounds_err
  ldr x2, [sp, #208]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L35:
  mov x0, #2
  str x0, [sp, #216]
.L36:
  mov x0, #42
  str x0, [sp, #224]
.L37:
  ldr x1, [sp, #216]
  cmp x1, #32
  b.hs .Lbounds_err
  ldr x2, [sp, #224]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L38:
  mov x0, #2
  str x0, [sp, #232]
.L39:
  ldr x1, [sp, #24]
  ldr x2, [sp, #232]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L47
.L40:
  mov x0, #25
  str x0, [sp, #240]
.L41:
  mov x0, #2
  str x0, [sp, #248]
.L42:
  ldr x2, [sp, #248]
  cbz x2, .Ldiv_by_zero
  ldr x1, [sp, #48]
  ldr x2, [sp, #248]
  sdiv x3, x1, x2
  msub x0, x3, x2, x1
  str x0, [sp, #256]
.L43:
  ldr x1, [sp, #240]
  cmp x1, #32
  b.hs .Lbounds_err
  ldr x2, [sp, #256]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L44:
  mov x0, #1
  str x0, [sp, #264]
.L45:
  ldr x1, [sp, #24]
  ldr x2, [sp, #264]
  add x0, x1, x2
  str x0, [sp, #24]
.L46:
  b .L38
.L47:
  ldr x0, [sp, #56]
  str x0, [sp, #56]
.L48:
  mov x0, #32
  str x0, [sp, #272]
.L49:
  ldr x2, [sp, #272]
  cbz x2, .Ldiv_by_zero
  ldr x1, [sp, #24]
  ldr x2, [sp, #272]
  sdiv x3, x1, x2
  msub x0, x3, x2, x1
  str x0, [sp, #280]
.L50:
  mov x0, #32
  str x0, [sp, #288]
.L51:
  ldr x1, [sp, #280]
  ldr x2, [sp, #288]
  add x0, x1, x2
  str x0, [sp, #296]
.L52:
  mov x0, #32
  str x0, [sp, #304]
.L53:
  ldr x2, [sp, #304]
  cbz x2, .Ldiv_by_zero
  ldr x1, [sp, #296]
  ldr x2, [sp, #304]
  sdiv x3, x1, x2
  msub x0, x3, x2, x1
  str x0, [sp, #312]
.L54:
  ldr x1, [sp, #312]
  cmp x1, #32
  b.hs .Lbounds_err
  ldr x2, [sp, #48]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L55:
  mov x0, #2
  str x0, [sp, #320]
.L56:
  ldr x1, [sp, #16]
  ldr x2, [sp, #320]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L61
.L57:
  ldr x0, [sp, #16]
  str x0, [sp, #16]
.L58:
  mov x0, #1
  str x0, [sp, #328]
.L59:
  ldr x1, [sp, #16]
  ldr x2, [sp, #328]
  add x0, x1, x2
  str x0, [sp, #16]
.L60:
  b .L55
.L61:
  mov x0, #2
  str x0, [sp, #336]
.L62:
  ldr x1, [sp, #48]
  ldr x2, [sp, #336]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L74
.L63:
  mov x0, #32
  str x0, [sp, #344]
.L64:
  ldr x2, [sp, #344]
  cbz x2, .Ldiv_by_zero
  ldr x1, [sp, #40]
  ldr x2, [sp, #344]
  sdiv x3, x1, x2
  msub x0, x3, x2, x1
  str x0, [sp, #352]
.L65:
  mov x0, #32
  str x0, [sp, #360]
.L66:
  ldr x1, [sp, #352]
  ldr x2, [sp, #360]
  add x0, x1, x2
  str x0, [sp, #368]
.L67:
  mov x0, #32
  str x0, [sp, #376]
.L68:
  ldr x2, [sp, #376]
  cbz x2, .Ldiv_by_zero
  ldr x1, [sp, #368]
  ldr x2, [sp, #376]
  sdiv x3, x1, x2
  msub x0, x3, x2, x1
  str x0, [sp, #384]
.L69:
  ldr x1, [sp, #384]
  cmp x1, #32
  b.hs .Lbounds_err
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #392]
.L70:
  ldr x0, [sp, #392]
  str x0, [sp, #48]
.L71:
  mov x0, #1
  str x0, [sp, #400]
.L72:
  ldr x1, [sp, #48]
  ldr x2, [sp, #400]
  add x0, x1, x2
  str x0, [sp, #48]
.L73:
  b .L61
.L74:
  ldr x1, [sp, #32]
  ldr x2, [sp, #16]
  cmp x1, x2
  cset w0, le
  cbnz w0, .L79
.L75:
  mov x0, #0
  str x0, [sp, #408]
.L76:
  ldr x1, [sp, #40]
  ldr x2, [sp, #408]
  cmp x1, x2
  cset w0, eq
  eor w0, w0, #1
  cbnz w0, .L79
.L77:
  mov x0, #0
  str x0, [sp, #416]
.L78:
  b .L80
.L79:
  mov x0, #1
  str x0, [sp, #416]
.L80:
  ldr x1, [sp, #416]
  mov x2, #0
  cmp x1, x2
  cset w0, ne
  cbnz w0, .L95
.L81:
  mov x0, #100
  str x0, [sp, #424]
.L82:
  ldr x1, [sp, #40]
  ldr x2, [sp, #424]
  cmp x1, x2
  cset w0, ne
  eor w0, w0, #1
  cbnz w0, .L86
.L83:
  mov x0, #42
  str x0, [sp, #432]
.L84:
  ldr x1, [sp, #8]
  ldr x2, [sp, #432]
  cmp x1, x2
  cset w0, le
  str x0, [sp, #64]
.L85:
  b .L94
.L86:
  mov x0, #1
  str x0, [sp, #440]
.L87:
  ldr x1, [sp, #48]
  ldr x2, [sp, #440]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L94
.L88:
  mov x0, #0
  str x0, [sp, #448]
.L89:
  mov x0, #1
  str x0, [sp, #456]
.L90:
  ldr x1, [sp, #448]
  ldr x2, [sp, #456]
  sub x0, x1, x2
  str x0, [sp, #32]
.L91:
  mov x0, #1
  str x0, [sp, #464]
.L92:
  ldr x1, [sp, #48]
  ldr x2, [sp, #464]
  add x0, x1, x2
  str x0, [sp, #48]
.L93:
  b .L86
.L94:
  b .L97
.L95:
  mov x0, #5
  str x0, [sp, #472]
.L96:
  ldr x1, [sp, #8]
  ldr x2, [sp, #472]
  cmp x1, x2
  cset w0, ne
  str x0, [sp, #56]
.L97:
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
