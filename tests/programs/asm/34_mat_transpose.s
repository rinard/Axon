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
  mov x0, #3
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
  mov x0, #0
  str x0, [sp, #16]
.L34:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L49
.L35:
  mov x0, #0
  str x0, [sp, #24]
.L36:
  ldr x1, [sp, #24]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L46
.L37:
  ldr x1, [sp, #24]
  ldr x2, [sp, #8]
  mul x0, x1, x2
  str x0, [sp, #192]
.L38:
  ldr x1, [sp, #192]
  ldr x2, [sp, #16]
  add x0, x1, x2
  str x0, [sp, #200]
.L39:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  mul x0, x1, x2
  str x0, [sp, #208]
.L40:
  ldr x1, [sp, #208]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #216]
.L41:
  ldr x1, [sp, #216]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #224]
.L42:
  ldr x1, [sp, #200]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #224]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L43:
  mov x0, #1
  str x0, [sp, #232]
.L44:
  ldr x1, [sp, #24]
  ldr x2, [sp, #232]
  add x0, x1, x2
  str x0, [sp, #24]
.L45:
  b .L36
.L46:
  mov x0, #1
  str x0, [sp, #240]
.L47:
  ldr x1, [sp, #16]
  ldr x2, [sp, #240]
  add x0, x1, x2
  str x0, [sp, #16]
.L48:
  b .L34
.L49:
  mov x0, #0
  str x0, [sp, #248]
.L50:
  ldr x1, [sp, #248]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #256]
.L51:
  movz x0, #57600
  movk x0, #1525, lsl #16
  str x0, [sp, #264]
.L52:
  ldr x1, [sp, #256]
  ldr x2, [sp, #264]
  mul x0, x1, x2
  str x0, [sp, #272]
.L53:
  mov x0, #1
  str x0, [sp, #280]
.L54:
  ldr x1, [sp, #280]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #288]
.L55:
  movz x0, #38528
  movk x0, #152, lsl #16
  str x0, [sp, #296]
.L56:
  ldr x1, [sp, #288]
  ldr x2, [sp, #296]
  mul x0, x1, x2
  str x0, [sp, #304]
.L57:
  ldr x1, [sp, #272]
  ldr x2, [sp, #304]
  add x0, x1, x2
  str x0, [sp, #312]
.L58:
  mov x0, #2
  str x0, [sp, #320]
.L59:
  ldr x1, [sp, #320]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #328]
.L60:
  movz x0, #16960
  movk x0, #15, lsl #16
  str x0, [sp, #336]
.L61:
  ldr x1, [sp, #328]
  ldr x2, [sp, #336]
  mul x0, x1, x2
  str x0, [sp, #344]
.L62:
  ldr x1, [sp, #312]
  ldr x2, [sp, #344]
  add x0, x1, x2
  str x0, [sp, #352]
.L63:
  mov x0, #3
  str x0, [sp, #360]
.L64:
  ldr x1, [sp, #360]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #368]
.L65:
  movz x0, #34464
  movk x0, #1, lsl #16
  str x0, [sp, #376]
.L66:
  ldr x1, [sp, #368]
  ldr x2, [sp, #376]
  mul x0, x1, x2
  str x0, [sp, #384]
.L67:
  ldr x1, [sp, #352]
  ldr x2, [sp, #384]
  add x0, x1, x2
  str x0, [sp, #392]
.L68:
  mov x0, #4
  str x0, [sp, #400]
.L69:
  ldr x1, [sp, #400]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #408]
.L70:
  mov x0, #10000
  str x0, [sp, #416]
.L71:
  ldr x1, [sp, #408]
  ldr x2, [sp, #416]
  mul x0, x1, x2
  str x0, [sp, #424]
.L72:
  ldr x1, [sp, #392]
  ldr x2, [sp, #424]
  add x0, x1, x2
  str x0, [sp, #432]
.L73:
  mov x0, #5
  str x0, [sp, #440]
.L74:
  ldr x1, [sp, #440]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #448]
.L75:
  mov x0, #1000
  str x0, [sp, #456]
.L76:
  ldr x1, [sp, #448]
  ldr x2, [sp, #456]
  mul x0, x1, x2
  str x0, [sp, #464]
.L77:
  ldr x1, [sp, #432]
  ldr x2, [sp, #464]
  add x0, x1, x2
  str x0, [sp, #472]
.L78:
  mov x0, #6
  str x0, [sp, #480]
.L79:
  ldr x1, [sp, #480]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #488]
.L80:
  mov x0, #100
  str x0, [sp, #496]
.L81:
  ldr x1, [sp, #488]
  ldr x2, [sp, #496]
  mul x0, x1, x2
  str x0, [sp, #504]
.L82:
  ldr x1, [sp, #472]
  ldr x2, [sp, #504]
  add x0, x1, x2
  str x0, [sp, #512]
.L83:
  mov x0, #7
  str x0, [sp, #520]
.L84:
  ldr x1, [sp, #520]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #528]
.L85:
  mov x0, #10
  str x0, [sp, #536]
.L86:
  ldr x1, [sp, #528]
  ldr x2, [sp, #536]
  mul x0, x1, x2
  str x0, [sp, #544]
.L87:
  ldr x1, [sp, #512]
  ldr x2, [sp, #544]
  add x0, x1, x2
  str x0, [sp, #552]
.L88:
  mov x0, #8
  str x0, [sp, #560]
.L89:
  ldr x1, [sp, #560]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #568]
.L90:
  ldr x1, [sp, #552]
  ldr x2, [sp, #568]
  add x0, x1, x2
  str x0, [sp, #40]
.L91:
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
  // print t
  ldr x9, [sp, #32]
  sub sp, sp, #16
  adrp x8, .Lname_t@PAGE
  add x8, x8, .Lname_t@PAGEOFF
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
.Lname_n:
  .asciz "n"
.Lname_i:
  .asciz "i"
.Lname_j:
  .asciz "j"
.Lname_t:
  .asciz "t"
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
