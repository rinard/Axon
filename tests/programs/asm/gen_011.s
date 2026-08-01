.global _main
.align 2

_main:
  sub sp, sp, #528
  str x30, [sp, #520]
  str x29, [sp, #512]
  add x29, sp, #512

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
  str x0, [sp, #480]
  str x0, [sp, #488]
  str x0, [sp, #496]
  str x0, [sp, #504]

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
  str x0, [sp, #32]
.L9:
  mov x0, #2
  str x0, [sp, #16]
.L10:
  mov x0, #100
  str x0, [sp, #48]
.L11:
  mov x0, #0
  str x0, [sp, #72]
.L12:
  mov x0, #1
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
  mov x0, #42
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
  mov x0, #1
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
  mov x0, #0
  str x0, [sp, #120]
.L21:
  mov x0, #0
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
  mov x0, #1
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
  mov x0, #2
  str x0, [sp, #152]
.L27:
  mov x0, #10
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
  mov x0, #3
  str x0, [sp, #168]
.L30:
  mov x0, #0
  str x0, [sp, #176]
.L31:
  mov x0, #5
  str x0, [sp, #184]
.L32:
  ldr x1, [sp, #176]
  ldr x2, [sp, #184]
  sub x0, x1, x2
  str x0, [sp, #192]
.L33:
  ldr x1, [sp, #168]
  cmp x1, #32
  b.hs .Lbounds_err
  ldr x2, [sp, #192]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L34:
  mov x0, #8
  str x0, [sp, #200]
.L35:
  ldr x1, [sp, #8]
  ldr x2, [sp, #200]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L49
.L36:
  mov x0, #6
  str x0, [sp, #208]
.L37:
  ldr x1, [sp, #32]
  ldr x2, [sp, #208]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L46
.L38:
  mov x0, #1
  str x0, [sp, #216]
.L39:
  ldr x1, [sp, #48]
  ldr x2, [sp, #216]
  cmp x1, x2
  cset w0, ne
  cbnz w0, .L42
.L40:
  ldr x0, [sp, #48]
  str x0, [sp, #24]
.L41:
  b .L43
.L42:
  ldr x0, [sp, #40]
  str x0, [sp, #24]
.L43:
  mov x0, #1
  str x0, [sp, #224]
.L44:
  ldr x1, [sp, #32]
  ldr x2, [sp, #224]
  add x0, x1, x2
  str x0, [sp, #32]
.L45:
  b .L36
.L46:
  mov x0, #1
  str x0, [sp, #232]
.L47:
  ldr x1, [sp, #8]
  ldr x2, [sp, #232]
  add x0, x1, x2
  str x0, [sp, #8]
.L48:
  b .L34
.L49:
  mov x0, #10
  str x0, [sp, #240]
.L50:
  ldr x1, [sp, #8]
  ldr x2, [sp, #240]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L57
.L51:
  mov x0, #3
  str x0, [sp, #248]
.L52:
  mov x0, #10
  str x0, [sp, #256]
.L53:
  ldr x1, [sp, #248]
  ldr x2, [sp, #256]
  sub x0, x1, x2
  str x0, [sp, #48]
.L54:
  mov x0, #1
  str x0, [sp, #264]
.L55:
  ldr x1, [sp, #8]
  ldr x2, [sp, #264]
  add x0, x1, x2
  str x0, [sp, #8]
.L56:
  b .L49
.L57:
  mov x0, #32
  str x0, [sp, #272]
.L58:
  ldr x2, [sp, #272]
  cbz x2, .Ldiv_by_zero
  ldr x1, [sp, #8]
  ldr x2, [sp, #272]
  sdiv x3, x1, x2
  msub x0, x3, x2, x1
  str x0, [sp, #280]
.L59:
  mov x0, #32
  str x0, [sp, #288]
.L60:
  ldr x1, [sp, #280]
  ldr x2, [sp, #288]
  add x0, x1, x2
  str x0, [sp, #296]
.L61:
  mov x0, #32
  str x0, [sp, #304]
.L62:
  ldr x2, [sp, #304]
  cbz x2, .Ldiv_by_zero
  ldr x1, [sp, #296]
  ldr x2, [sp, #304]
  sdiv x3, x1, x2
  msub x0, x3, x2, x1
  str x0, [sp, #312]
.L63:
  ldr x1, [sp, #312]
  cmp x1, #32
  b.hs .Lbounds_err
  ldr x2, [sp, #8]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L64:
  mov x0, #32
  str x0, [sp, #320]
.L65:
  ldr x2, [sp, #320]
  cbz x2, .Ldiv_by_zero
  ldr x1, [sp, #40]
  ldr x2, [sp, #320]
  sdiv x3, x1, x2
  msub x0, x3, x2, x1
  str x0, [sp, #328]
.L66:
  mov x0, #32
  str x0, [sp, #336]
.L67:
  ldr x1, [sp, #328]
  ldr x2, [sp, #336]
  add x0, x1, x2
  str x0, [sp, #344]
.L68:
  mov x0, #32
  str x0, [sp, #352]
.L69:
  ldr x2, [sp, #352]
  cbz x2, .Ldiv_by_zero
  ldr x1, [sp, #344]
  ldr x2, [sp, #352]
  sdiv x3, x1, x2
  msub x0, x3, x2, x1
  str x0, [sp, #360]
.L70:
  ldr x1, [sp, #360]
  cmp x1, #32
  b.hs .Lbounds_err
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #368]
.L71:
  ldr x0, [sp, #368]
  str x0, [sp, #24]
.L72:
  mov x0, #10
  str x0, [sp, #376]
.L73:
  mov x0, #9
  str x0, [sp, #384]
.L74:
  ldr x1, [sp, #384]
  cmp x1, #32
  b.hs .Lbounds_err
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #392]
.L75:
  ldr x1, [sp, #376]
  ldr x2, [sp, #392]
  cmp x1, x2
  cset w0, le
  cbnz w0, .L97
.L76:
  mov x0, #0
  str x0, [sp, #400]
.L77:
  mov x0, #5
  str x0, [sp, #408]
.L78:
  ldr x1, [sp, #400]
  ldr x2, [sp, #408]
  sub x0, x1, x2
  str x0, [sp, #416]
.L79:
  ldr x1, [sp, #24]
  ldr x2, [sp, #416]
  cmp x1, x2
  cset w0, ne
  cbnz w0, .L84
.L80:
  mov x0, #42
  str x0, [sp, #424]
.L81:
  ldr x1, [sp, #8]
  ldr x2, [sp, #424]
  cmp x1, x2
  cset w0, le
  cbnz w0, .L84
.L82:
  mov x0, #0
  str x0, [sp, #432]
.L83:
  b .L85
.L84:
  mov x0, #1
  str x0, [sp, #432]
.L85:
  ldr x1, [sp, #432]
  mov x2, #0
  cmp x1, x2
  cset w0, ne
  cbnz w0, .L90
.L86:
  mov x0, #24
  str x0, [sp, #440]
.L87:
  mov x0, #42
  str x0, [sp, #448]
.L88:
  ldr x1, [sp, #440]
  cmp x1, #32
  b.hs .Lbounds_err
  ldr x2, [sp, #448]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L89:
  b .L96
.L90:
  mov x0, #5
  str x0, [sp, #456]
.L91:
  ldr x1, [sp, #40]
  ldr x2, [sp, #456]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L96
.L92:
  ldr x0, [sp, #48]
  str x0, [sp, #48]
.L93:
  mov x0, #1
  str x0, [sp, #464]
.L94:
  ldr x1, [sp, #40]
  ldr x2, [sp, #464]
  add x0, x1, x2
  str x0, [sp, #40]
.L95:
  b .L90
.L96:
  b .L98
.L97:
  ldr x0, [sp, #24]
  str x0, [sp, #48]
.L98:
  mov x0, #0
  str x0, [sp, #472]
.L99:
  mov x0, #5
  str x0, [sp, #480]
.L100:
  ldr x1, [sp, #472]
  ldr x2, [sp, #480]
  sub x0, x1, x2
  str x0, [sp, #488]
.L101:
  ldr x1, [sp, #8]
  ldr x2, [sp, #488]
  cmp x1, x2
  cset w0, eq
  cbnz w0, .L106
.L102:
  mov x0, #0
  str x0, [sp, #496]
.L103:
  ldr x1, [sp, #24]
  ldr x2, [sp, #496]
  cmp x1, x2
  cset w0, ne
  cbnz w0, .L106
.L104:
  mov x0, #0
  str x0, [sp, #504]
.L105:
  b .L107
.L106:
  mov x0, #1
  str x0, [sp, #504]
.L107:
  ldr x1, [sp, #504]
  mov x2, #0
  cmp x1, x2
  cset w0, ne
  eor w0, w0, #1
  str x0, [sp, #64]
.L108:
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
  ldr x29, [sp, #512]
  ldr x30, [sp, #520]
  add sp, sp, #528
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
