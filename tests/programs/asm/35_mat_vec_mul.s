.global _main
.align 2

_main:
  sub sp, sp, #576
  str x30, [sp, #568]
  str x29, [sp, #560]
  add x29, sp, #560

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
  mov x0, #4
  str x0, [sp, #8]
.L6:
  mov x0, #0
  str x0, [sp, #48]
.L7:
  mov x0, #1
  str x0, [sp, #56]
.L8:
  ldr x1, [sp, #48]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #56]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L9:
  mov x0, #1
  str x0, [sp, #64]
.L10:
  mov x0, #2
  str x0, [sp, #72]
.L11:
  ldr x1, [sp, #64]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #72]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L12:
  mov x0, #2
  str x0, [sp, #80]
.L13:
  mov x0, #3
  str x0, [sp, #88]
.L14:
  ldr x1, [sp, #80]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #88]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L15:
  mov x0, #3
  str x0, [sp, #96]
.L16:
  mov x0, #4
  str x0, [sp, #104]
.L17:
  ldr x1, [sp, #96]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #104]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L18:
  mov x0, #4
  str x0, [sp, #112]
.L19:
  mov x0, #5
  str x0, [sp, #120]
.L20:
  ldr x1, [sp, #112]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #120]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L21:
  mov x0, #5
  str x0, [sp, #128]
.L22:
  mov x0, #6
  str x0, [sp, #136]
.L23:
  ldr x1, [sp, #128]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #136]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L24:
  mov x0, #6
  str x0, [sp, #144]
.L25:
  mov x0, #7
  str x0, [sp, #152]
.L26:
  ldr x1, [sp, #144]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #152]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L27:
  mov x0, #7
  str x0, [sp, #160]
.L28:
  mov x0, #8
  str x0, [sp, #168]
.L29:
  ldr x1, [sp, #160]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #168]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L30:
  mov x0, #8
  str x0, [sp, #176]
.L31:
  mov x0, #9
  str x0, [sp, #184]
.L32:
  ldr x1, [sp, #176]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #184]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L33:
  mov x0, #9
  str x0, [sp, #192]
.L34:
  mov x0, #10
  str x0, [sp, #200]
.L35:
  ldr x1, [sp, #192]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #200]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L36:
  mov x0, #10
  str x0, [sp, #208]
.L37:
  mov x0, #11
  str x0, [sp, #216]
.L38:
  ldr x1, [sp, #208]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #216]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L39:
  mov x0, #11
  str x0, [sp, #224]
.L40:
  mov x0, #12
  str x0, [sp, #232]
.L41:
  ldr x1, [sp, #224]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #232]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L42:
  mov x0, #12
  str x0, [sp, #240]
.L43:
  mov x0, #13
  str x0, [sp, #248]
.L44:
  ldr x1, [sp, #240]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #248]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L45:
  mov x0, #13
  str x0, [sp, #256]
.L46:
  mov x0, #14
  str x0, [sp, #264]
.L47:
  ldr x1, [sp, #256]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #264]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L48:
  mov x0, #14
  str x0, [sp, #272]
.L49:
  mov x0, #15
  str x0, [sp, #280]
.L50:
  ldr x1, [sp, #272]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #280]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L51:
  mov x0, #15
  str x0, [sp, #288]
.L52:
  mov x0, #16
  str x0, [sp, #296]
.L53:
  ldr x1, [sp, #288]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #296]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L54:
  mov x0, #0
  str x0, [sp, #304]
.L55:
  mov x0, #1
  str x0, [sp, #312]
.L56:
  ldr x1, [sp, #304]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #312]
  adrp x8, _arr_X@PAGE
  add x8, x8, _arr_X@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L57:
  mov x0, #1
  str x0, [sp, #320]
.L58:
  mov x0, #2
  str x0, [sp, #328]
.L59:
  ldr x1, [sp, #320]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #328]
  adrp x8, _arr_X@PAGE
  add x8, x8, _arr_X@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L60:
  mov x0, #2
  str x0, [sp, #336]
.L61:
  mov x0, #3
  str x0, [sp, #344]
.L62:
  ldr x1, [sp, #336]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #344]
  adrp x8, _arr_X@PAGE
  add x8, x8, _arr_X@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L63:
  mov x0, #3
  str x0, [sp, #352]
.L64:
  mov x0, #4
  str x0, [sp, #360]
.L65:
  ldr x1, [sp, #352]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #360]
  adrp x8, _arr_X@PAGE
  add x8, x8, _arr_X@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L66:
  mov x0, #0
  str x0, [sp, #16]
.L67:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L84
.L68:
  mov x0, #0
  str x0, [sp, #32]
.L69:
  mov x0, #0
  str x0, [sp, #24]
.L70:
  ldr x1, [sp, #24]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L80
.L71:
  ldr x1, [sp, #16]
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
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #384]
.L74:
  ldr x1, [sp, #24]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_X@PAGE
  add x8, x8, _arr_X@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #392]
.L75:
  ldr x1, [sp, #384]
  ldr x2, [sp, #392]
  mul x0, x1, x2
  str x0, [sp, #400]
.L76:
  ldr x1, [sp, #32]
  ldr x2, [sp, #400]
  add x0, x1, x2
  str x0, [sp, #32]
.L77:
  mov x0, #1
  str x0, [sp, #408]
.L78:
  ldr x1, [sp, #24]
  ldr x2, [sp, #408]
  add x0, x1, x2
  str x0, [sp, #24]
.L79:
  b .L70
.L80:
  ldr x1, [sp, #16]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #32]
  adrp x8, _arr_Y@PAGE
  add x8, x8, _arr_Y@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L81:
  mov x0, #1
  str x0, [sp, #416]
.L82:
  ldr x1, [sp, #16]
  ldr x2, [sp, #416]
  add x0, x1, x2
  str x0, [sp, #16]
.L83:
  b .L67
.L84:
  mov x0, #0
  str x0, [sp, #424]
.L85:
  ldr x1, [sp, #424]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_Y@PAGE
  add x8, x8, _arr_Y@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #432]
.L86:
  movz x0, #16960
  movk x0, #15, lsl #16
  str x0, [sp, #440]
.L87:
  ldr x1, [sp, #432]
  ldr x2, [sp, #440]
  mul x0, x1, x2
  str x0, [sp, #448]
.L88:
  mov x0, #1
  str x0, [sp, #456]
.L89:
  ldr x1, [sp, #456]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_Y@PAGE
  add x8, x8, _arr_Y@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #464]
.L90:
  mov x0, #10000
  str x0, [sp, #472]
.L91:
  ldr x1, [sp, #464]
  ldr x2, [sp, #472]
  mul x0, x1, x2
  str x0, [sp, #480]
.L92:
  ldr x1, [sp, #448]
  ldr x2, [sp, #480]
  add x0, x1, x2
  str x0, [sp, #488]
.L93:
  mov x0, #2
  str x0, [sp, #496]
.L94:
  ldr x1, [sp, #496]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_Y@PAGE
  add x8, x8, _arr_Y@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #504]
.L95:
  mov x0, #100
  str x0, [sp, #512]
.L96:
  ldr x1, [sp, #504]
  ldr x2, [sp, #512]
  mul x0, x1, x2
  str x0, [sp, #520]
.L97:
  ldr x1, [sp, #488]
  ldr x2, [sp, #520]
  add x0, x1, x2
  str x0, [sp, #528]
.L98:
  mov x0, #3
  str x0, [sp, #536]
.L99:
  ldr x1, [sp, #536]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_Y@PAGE
  add x8, x8, _arr_Y@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #544]
.L100:
  ldr x1, [sp, #528]
  ldr x2, [sp, #544]
  add x0, x1, x2
  str x0, [sp, #40]
.L101:
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
  ldr x29, [sp, #560]
  ldr x30, [sp, #568]
  add sp, sp, #576
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
.global _arr_X
.align 3
_arr_X:
  .space 8192
.global _arr_Y
.align 3
_arr_Y:
  .space 8192
