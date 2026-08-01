.global _main
.align 2

_main:
  sub sp, sp, #592
  str x30, [sp, #584]
  str x29, [sp, #576]
  add x29, sp, #576

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
  str x0, [sp, #512]
  str x0, [sp, #520]
  str x0, [sp, #528]
  str x0, [sp, #536]
  str x0, [sp, #544]
  str x0, [sp, #552]
  str x0, [sp, #560]
  str x0, [sp, #568]

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
  mov x0, #2
  str x0, [sp, #8]
.L9:
  mov x0, #0
  str x0, [sp, #72]
.L10:
  mov x0, #5
  str x0, [sp, #80]
.L11:
  ldr x1, [sp, #72]
  ldr x2, [sp, #80]
  sub x0, x1, x2
  str x0, [sp, #48]
.L12:
  mov x0, #2
  str x0, [sp, #40]
.L13:
  mov x0, #0
  str x0, [sp, #88]
.L14:
  mov x0, #0
  str x0, [sp, #96]
.L15:
  mov x0, #1
  str x0, [sp, #104]
.L16:
  ldr x1, [sp, #96]
  ldr x2, [sp, #104]
  sub x0, x1, x2
  str x0, [sp, #112]
.L17:
  ldr x1, [sp, #88]
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
  mov x0, #10
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
  mov x0, #100
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
  mov x0, #5
  str x0, [sp, #192]
.L32:
  ldr x1, [sp, #184]
  cmp x1, #32
  b.hs .Lbounds_err
  ldr x2, [sp, #192]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L33:
  mov x0, #2
  str x0, [sp, #200]
.L34:
  mov x0, #100
  str x0, [sp, #208]
.L35:
  ldr x1, [sp, #200]
  cmp x1, #32
  b.hs .Lbounds_err
  ldr x2, [sp, #208]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L36:
  mov x0, #3
  str x0, [sp, #216]
.L37:
  mov x0, #0
  str x0, [sp, #224]
.L38:
  ldr x1, [sp, #216]
  cmp x1, #32
  b.hs .Lbounds_err
  ldr x2, [sp, #224]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L39:
  mov x0, #5
  str x0, [sp, #232]
.L40:
  ldr x1, [sp, #8]
  ldr x2, [sp, #16]
  mul x0, x1, x2
  str x0, [sp, #240]
.L41:
  ldr x1, [sp, #232]
  ldr x2, [sp, #240]
  cmp x1, x2
  cset w0, lt
  cbnz w0, .L54
.L42:
  mov x0, #9
  str x0, [sp, #248]
.L43:
  ldr x1, [sp, #40]
  ldr x2, [sp, #248]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L53
.L44:
  mov x0, #6
  str x0, [sp, #256]
.L45:
  ldr x1, [sp, #48]
  ldr x2, [sp, #256]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L50
.L46:
  ldr x0, [sp, #8]
  str x0, [sp, #32]
.L47:
  mov x0, #1
  str x0, [sp, #264]
.L48:
  ldr x1, [sp, #48]
  ldr x2, [sp, #264]
  add x0, x1, x2
  str x0, [sp, #48]
.L49:
  b .L44
.L50:
  mov x0, #1
  str x0, [sp, #272]
.L51:
  ldr x1, [sp, #40]
  ldr x2, [sp, #272]
  add x0, x1, x2
  str x0, [sp, #40]
.L52:
  b .L42
.L53:
  b .L65
.L54:
  mov x0, #9
  str x0, [sp, #280]
.L55:
  ldr x1, [sp, #16]
  ldr x2, [sp, #280]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L65
.L56:
  mov x0, #9
  str x0, [sp, #288]
.L57:
  ldr x1, [sp, #32]
  ldr x2, [sp, #288]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L62
.L58:
  ldr x0, [sp, #16]
  str x0, [sp, #40]
.L59:
  mov x0, #1
  str x0, [sp, #296]
.L60:
  ldr x1, [sp, #32]
  ldr x2, [sp, #296]
  add x0, x1, x2
  str x0, [sp, #32]
.L61:
  b .L56
.L62:
  mov x0, #1
  str x0, [sp, #304]
.L63:
  ldr x1, [sp, #16]
  ldr x2, [sp, #304]
  add x0, x1, x2
  str x0, [sp, #16]
.L64:
  b .L54
.L65:
  mov x0, #4
  str x0, [sp, #312]
.L66:
  ldr x1, [sp, #24]
  ldr x2, [sp, #312]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L72
.L67:
  mov x0, #42
  str x0, [sp, #320]
.L68:
  ldr x1, [sp, #320]
  ldr x2, [sp, #48]
  add x0, x1, x2
  str x0, [sp, #40]
.L69:
  mov x0, #1
  str x0, [sp, #328]
.L70:
  ldr x1, [sp, #24]
  ldr x2, [sp, #328]
  add x0, x1, x2
  str x0, [sp, #24]
.L71:
  b .L65
.L72:
  mov x0, #5
  str x0, [sp, #336]
.L73:
  ldr x1, [sp, #16]
  ldr x2, [sp, #336]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L85
.L74:
  mov x0, #32
  str x0, [sp, #344]
.L75:
  ldr x2, [sp, #344]
  cbz x2, .Ldiv_by_zero
  ldr x1, [sp, #40]
  ldr x2, [sp, #344]
  sdiv x3, x1, x2
  msub x0, x3, x2, x1
  str x0, [sp, #352]
.L76:
  mov x0, #32
  str x0, [sp, #360]
.L77:
  ldr x1, [sp, #352]
  ldr x2, [sp, #360]
  add x0, x1, x2
  str x0, [sp, #368]
.L78:
  mov x0, #32
  str x0, [sp, #376]
.L79:
  ldr x2, [sp, #376]
  cbz x2, .Ldiv_by_zero
  ldr x1, [sp, #368]
  ldr x2, [sp, #376]
  sdiv x3, x1, x2
  msub x0, x3, x2, x1
  str x0, [sp, #384]
.L80:
  ldr x1, [sp, #48]
  ldr x2, [sp, #48]
  mul x0, x1, x2
  str x0, [sp, #392]
.L81:
  ldr x1, [sp, #384]
  cmp x1, #32
  b.hs .Lbounds_err
  ldr x2, [sp, #392]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L82:
  mov x0, #1
  str x0, [sp, #400]
.L83:
  ldr x1, [sp, #16]
  ldr x2, [sp, #400]
  add x0, x1, x2
  str x0, [sp, #16]
.L84:
  b .L72
.L85:
  mov x0, #14
  str x0, [sp, #408]
.L86:
  mov x0, #0
  str x0, [sp, #416]
.L87:
  ldr x1, [sp, #408]
  cmp x1, #32
  b.hs .Lbounds_err
  ldr x2, [sp, #416]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L88:
  mov x0, #0
  str x0, [sp, #424]
.L89:
  mov x0, #5
  str x0, [sp, #432]
.L90:
  ldr x1, [sp, #424]
  ldr x2, [sp, #432]
  sub x0, x1, x2
  str x0, [sp, #440]
.L91:
  mov x0, #1
  str x0, [sp, #448]
.L92:
  ldr x1, [sp, #440]
  ldr x2, [sp, #448]
  cmp x1, x2
  cset w0, le
  cbnz w0, .L95
.L93:
  ldr x1, [sp, #8]
  ldr x2, [sp, #32]
  add x0, x1, x2
  str x0, [sp, #32]
.L94:
  b .L107
.L95:
  mov x0, #2
  str x0, [sp, #456]
.L96:
  ldr x1, [sp, #24]
  ldr x2, [sp, #456]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L107
.L97:
  mov x0, #32
  str x0, [sp, #464]
.L98:
  ldr x2, [sp, #464]
  cbz x2, .Ldiv_by_zero
  ldr x1, [sp, #16]
  ldr x2, [sp, #464]
  sdiv x3, x1, x2
  msub x0, x3, x2, x1
  str x0, [sp, #472]
.L99:
  mov x0, #32
  str x0, [sp, #480]
.L100:
  ldr x1, [sp, #472]
  ldr x2, [sp, #480]
  add x0, x1, x2
  str x0, [sp, #488]
.L101:
  mov x0, #32
  str x0, [sp, #496]
.L102:
  ldr x2, [sp, #496]
  cbz x2, .Ldiv_by_zero
  ldr x1, [sp, #488]
  ldr x2, [sp, #496]
  sdiv x3, x1, x2
  msub x0, x3, x2, x1
  str x0, [sp, #504]
.L103:
  ldr x1, [sp, #504]
  cmp x1, #32
  b.hs .Lbounds_err
  ldr x2, [sp, #16]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L104:
  mov x0, #1
  str x0, [sp, #512]
.L105:
  ldr x1, [sp, #24]
  ldr x2, [sp, #512]
  add x0, x1, x2
  str x0, [sp, #24]
.L106:
  b .L95
.L107:
  mov x0, #32
  str x0, [sp, #520]
.L108:
  ldr x2, [sp, #520]
  cbz x2, .Ldiv_by_zero
  ldr x1, [sp, #48]
  ldr x2, [sp, #520]
  sdiv x3, x1, x2
  msub x0, x3, x2, x1
  str x0, [sp, #528]
.L109:
  mov x0, #32
  str x0, [sp, #536]
.L110:
  ldr x1, [sp, #528]
  ldr x2, [sp, #536]
  add x0, x1, x2
  str x0, [sp, #544]
.L111:
  mov x0, #32
  str x0, [sp, #552]
.L112:
  ldr x2, [sp, #552]
  cbz x2, .Ldiv_by_zero
  ldr x1, [sp, #544]
  ldr x2, [sp, #552]
  sdiv x3, x1, x2
  msub x0, x3, x2, x1
  str x0, [sp, #560]
.L113:
  mov x0, #10
  str x0, [sp, #568]
.L114:
  ldr x1, [sp, #560]
  cmp x1, #32
  b.hs .Lbounds_err
  ldr x2, [sp, #568]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L115:
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
  ldr x29, [sp, #576]
  ldr x30, [sp, #584]
  add sp, sp, #592
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
