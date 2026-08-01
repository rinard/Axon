.global _main
.align 2

_main:
  sub sp, sp, #544
  str x30, [sp, #536]
  str x29, [sp, #528]
  add x29, sp, #528

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
  mov x0, #3
  str x0, [sp, #8]
.L7:
  mov x0, #0
  str x0, [sp, #56]
.L8:
  mov x0, #1
  str x0, [sp, #64]
.L9:
  ldr x1, [sp, #56]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #64]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L10:
  mov x0, #1
  str x0, [sp, #72]
.L11:
  mov x0, #2
  str x0, [sp, #80]
.L12:
  ldr x1, [sp, #72]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #80]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L13:
  mov x0, #2
  str x0, [sp, #88]
.L14:
  mov x0, #3
  str x0, [sp, #96]
.L15:
  ldr x1, [sp, #88]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #96]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L16:
  mov x0, #3
  str x0, [sp, #104]
.L17:
  mov x0, #4
  str x0, [sp, #112]
.L18:
  ldr x1, [sp, #104]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #112]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L19:
  mov x0, #4
  str x0, [sp, #120]
.L20:
  mov x0, #5
  str x0, [sp, #128]
.L21:
  ldr x1, [sp, #120]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #128]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L22:
  mov x0, #5
  str x0, [sp, #136]
.L23:
  mov x0, #6
  str x0, [sp, #144]
.L24:
  ldr x1, [sp, #136]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #144]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L25:
  mov x0, #6
  str x0, [sp, #152]
.L26:
  mov x0, #7
  str x0, [sp, #160]
.L27:
  ldr x1, [sp, #152]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #160]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L28:
  mov x0, #7
  str x0, [sp, #168]
.L29:
  mov x0, #8
  str x0, [sp, #176]
.L30:
  ldr x1, [sp, #168]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #176]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L31:
  mov x0, #8
  str x0, [sp, #184]
.L32:
  mov x0, #9
  str x0, [sp, #192]
.L33:
  ldr x1, [sp, #184]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #192]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L34:
  mov x0, #0
  str x0, [sp, #200]
.L35:
  mov x0, #9
  str x0, [sp, #208]
.L36:
  ldr x1, [sp, #200]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #208]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L37:
  mov x0, #1
  str x0, [sp, #216]
.L38:
  mov x0, #8
  str x0, [sp, #224]
.L39:
  ldr x1, [sp, #216]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #224]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L40:
  mov x0, #2
  str x0, [sp, #232]
.L41:
  mov x0, #7
  str x0, [sp, #240]
.L42:
  ldr x1, [sp, #232]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #240]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L43:
  mov x0, #3
  str x0, [sp, #248]
.L44:
  mov x0, #6
  str x0, [sp, #256]
.L45:
  ldr x1, [sp, #248]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #256]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L46:
  mov x0, #4
  str x0, [sp, #264]
.L47:
  mov x0, #5
  str x0, [sp, #272]
.L48:
  ldr x1, [sp, #264]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #272]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L49:
  mov x0, #5
  str x0, [sp, #280]
.L50:
  mov x0, #4
  str x0, [sp, #288]
.L51:
  ldr x1, [sp, #280]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #288]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L52:
  mov x0, #6
  str x0, [sp, #296]
.L53:
  mov x0, #3
  str x0, [sp, #304]
.L54:
  ldr x1, [sp, #296]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #304]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L55:
  mov x0, #7
  str x0, [sp, #312]
.L56:
  mov x0, #2
  str x0, [sp, #320]
.L57:
  ldr x1, [sp, #312]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #320]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L58:
  mov x0, #8
  str x0, [sp, #328]
.L59:
  mov x0, #1
  str x0, [sp, #336]
.L60:
  ldr x1, [sp, #328]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #336]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L61:
  mov x0, #0
  str x0, [sp, #16]
.L62:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L88
.L63:
  mov x0, #0
  str x0, [sp, #24]
.L64:
  ldr x1, [sp, #24]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L85
.L65:
  mov x0, #0
  str x0, [sp, #40]
.L66:
  mov x0, #0
  str x0, [sp, #32]
.L67:
  ldr x1, [sp, #32]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L79
.L68:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  mul x0, x1, x2
  str x0, [sp, #344]
.L69:
  ldr x1, [sp, #344]
  ldr x2, [sp, #32]
  add x0, x1, x2
  str x0, [sp, #352]
.L70:
  ldr x1, [sp, #352]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #360]
.L71:
  ldr x1, [sp, #32]
  ldr x2, [sp, #8]
  mul x0, x1, x2
  str x0, [sp, #368]
.L72:
  ldr x1, [sp, #368]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #376]
.L73:
  ldr x1, [sp, #376]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #384]
.L74:
  ldr x1, [sp, #360]
  ldr x2, [sp, #384]
  mul x0, x1, x2
  str x0, [sp, #392]
.L75:
  ldr x1, [sp, #40]
  ldr x2, [sp, #392]
  add x0, x1, x2
  str x0, [sp, #40]
.L76:
  mov x0, #1
  str x0, [sp, #400]
.L77:
  ldr x1, [sp, #32]
  ldr x2, [sp, #400]
  add x0, x1, x2
  str x0, [sp, #32]
.L78:
  b .L67
.L79:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  mul x0, x1, x2
  str x0, [sp, #408]
.L80:
  ldr x1, [sp, #408]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #416]
.L81:
  ldr x1, [sp, #416]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #40]
  adrp x8, _arr_C@PAGE
  add x8, x8, _arr_C@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L82:
  mov x0, #1
  str x0, [sp, #424]
.L83:
  ldr x1, [sp, #24]
  ldr x2, [sp, #424]
  add x0, x1, x2
  str x0, [sp, #24]
.L84:
  b .L64
.L85:
  mov x0, #1
  str x0, [sp, #432]
.L86:
  ldr x1, [sp, #16]
  ldr x2, [sp, #432]
  add x0, x1, x2
  str x0, [sp, #16]
.L87:
  b .L62
.L88:
  mov x0, #0
  str x0, [sp, #440]
.L89:
  ldr x1, [sp, #440]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_C@PAGE
  add x8, x8, _arr_C@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #448]
.L90:
  mov x0, #100
  str x0, [sp, #456]
.L91:
  ldr x1, [sp, #448]
  ldr x2, [sp, #456]
  mul x0, x1, x2
  str x0, [sp, #464]
.L92:
  mov x0, #1
  str x0, [sp, #472]
.L93:
  ldr x1, [sp, #472]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_C@PAGE
  add x8, x8, _arr_C@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #480]
.L94:
  mov x0, #10
  str x0, [sp, #488]
.L95:
  ldr x1, [sp, #480]
  ldr x2, [sp, #488]
  mul x0, x1, x2
  str x0, [sp, #496]
.L96:
  ldr x1, [sp, #464]
  ldr x2, [sp, #496]
  add x0, x1, x2
  str x0, [sp, #504]
.L97:
  mov x0, #2
  str x0, [sp, #512]
.L98:
  ldr x1, [sp, #512]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_C@PAGE
  add x8, x8, _arr_C@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #520]
.L99:
  ldr x1, [sp, #504]
  ldr x2, [sp, #520]
  add x0, x1, x2
  str x0, [sp, #48]
.L100:
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
  // print r
  ldr x9, [sp, #48]
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
  ldr x29, [sp, #528]
  ldr x30, [sp, #536]
  add sp, sp, #544
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
