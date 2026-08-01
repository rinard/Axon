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
  mov x0, #6
  str x0, [sp, #8]
.L5:
  mov x0, #3
  str x0, [sp, #16]
.L6:
  mov x0, #0
  str x0, [sp, #40]
.L7:
  mov x0, #1
  str x0, [sp, #48]
.L8:
  ldr x1, [sp, #40]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #48]
  adrp x8, _arr_X@PAGE
  add x8, x8, _arr_X@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L9:
  mov x0, #1
  str x0, [sp, #56]
.L10:
  mov x0, #2
  str x0, [sp, #64]
.L11:
  ldr x1, [sp, #56]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #64]
  adrp x8, _arr_X@PAGE
  add x8, x8, _arr_X@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L12:
  mov x0, #2
  str x0, [sp, #72]
.L13:
  mov x0, #3
  str x0, [sp, #80]
.L14:
  ldr x1, [sp, #72]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #80]
  adrp x8, _arr_X@PAGE
  add x8, x8, _arr_X@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L15:
  mov x0, #3
  str x0, [sp, #88]
.L16:
  mov x0, #4
  str x0, [sp, #96]
.L17:
  ldr x1, [sp, #88]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #96]
  adrp x8, _arr_X@PAGE
  add x8, x8, _arr_X@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L18:
  mov x0, #4
  str x0, [sp, #104]
.L19:
  mov x0, #5
  str x0, [sp, #112]
.L20:
  ldr x1, [sp, #104]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #112]
  adrp x8, _arr_X@PAGE
  add x8, x8, _arr_X@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L21:
  mov x0, #5
  str x0, [sp, #120]
.L22:
  mov x0, #6
  str x0, [sp, #128]
.L23:
  ldr x1, [sp, #120]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #128]
  adrp x8, _arr_X@PAGE
  add x8, x8, _arr_X@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L24:
  mov x0, #0
  str x0, [sp, #136]
.L25:
  mov x0, #10
  str x0, [sp, #144]
.L26:
  ldr x1, [sp, #136]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #144]
  adrp x8, _arr_Y@PAGE
  add x8, x8, _arr_Y@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L27:
  mov x0, #1
  str x0, [sp, #152]
.L28:
  mov x0, #20
  str x0, [sp, #160]
.L29:
  ldr x1, [sp, #152]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #160]
  adrp x8, _arr_Y@PAGE
  add x8, x8, _arr_Y@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L30:
  mov x0, #2
  str x0, [sp, #168]
.L31:
  mov x0, #30
  str x0, [sp, #176]
.L32:
  ldr x1, [sp, #168]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #176]
  adrp x8, _arr_Y@PAGE
  add x8, x8, _arr_Y@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L33:
  mov x0, #3
  str x0, [sp, #184]
.L34:
  mov x0, #40
  str x0, [sp, #192]
.L35:
  ldr x1, [sp, #184]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #192]
  adrp x8, _arr_Y@PAGE
  add x8, x8, _arr_Y@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L36:
  mov x0, #4
  str x0, [sp, #200]
.L37:
  mov x0, #50
  str x0, [sp, #208]
.L38:
  ldr x1, [sp, #200]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #208]
  adrp x8, _arr_Y@PAGE
  add x8, x8, _arr_Y@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L39:
  mov x0, #5
  str x0, [sp, #216]
.L40:
  mov x0, #60
  str x0, [sp, #224]
.L41:
  ldr x1, [sp, #216]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #224]
  adrp x8, _arr_Y@PAGE
  add x8, x8, _arr_Y@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L42:
  mov x0, #0
  str x0, [sp, #24]
.L43:
  ldr x1, [sp, #24]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L52
.L44:
  ldr x1, [sp, #24]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_X@PAGE
  add x8, x8, _arr_X@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #232]
.L45:
  ldr x1, [sp, #16]
  ldr x2, [sp, #232]
  mul x0, x1, x2
  str x0, [sp, #240]
.L46:
  ldr x1, [sp, #24]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_Y@PAGE
  add x8, x8, _arr_Y@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #248]
.L47:
  ldr x1, [sp, #240]
  ldr x2, [sp, #248]
  add x0, x1, x2
  str x0, [sp, #256]
.L48:
  ldr x1, [sp, #24]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #256]
  adrp x8, _arr_Y@PAGE
  add x8, x8, _arr_Y@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L49:
  mov x0, #1
  str x0, [sp, #264]
.L50:
  ldr x1, [sp, #24]
  ldr x2, [sp, #264]
  add x0, x1, x2
  str x0, [sp, #24]
.L51:
  b .L43
.L52:
  mov x0, #0
  str x0, [sp, #272]
.L53:
  ldr x1, [sp, #272]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_Y@PAGE
  add x8, x8, _arr_Y@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #280]
.L54:
  movz x0, #34464
  movk x0, #1, lsl #16
  str x0, [sp, #288]
.L55:
  ldr x1, [sp, #280]
  ldr x2, [sp, #288]
  mul x0, x1, x2
  str x0, [sp, #296]
.L56:
  mov x0, #1
  str x0, [sp, #304]
.L57:
  ldr x1, [sp, #304]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_Y@PAGE
  add x8, x8, _arr_Y@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #312]
.L58:
  mov x0, #10000
  str x0, [sp, #320]
.L59:
  ldr x1, [sp, #312]
  ldr x2, [sp, #320]
  mul x0, x1, x2
  str x0, [sp, #328]
.L60:
  ldr x1, [sp, #296]
  ldr x2, [sp, #328]
  add x0, x1, x2
  str x0, [sp, #336]
.L61:
  mov x0, #2
  str x0, [sp, #344]
.L62:
  ldr x1, [sp, #344]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_Y@PAGE
  add x8, x8, _arr_Y@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #352]
.L63:
  mov x0, #1000
  str x0, [sp, #360]
.L64:
  ldr x1, [sp, #352]
  ldr x2, [sp, #360]
  mul x0, x1, x2
  str x0, [sp, #368]
.L65:
  ldr x1, [sp, #336]
  ldr x2, [sp, #368]
  add x0, x1, x2
  str x0, [sp, #376]
.L66:
  mov x0, #3
  str x0, [sp, #384]
.L67:
  ldr x1, [sp, #384]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_Y@PAGE
  add x8, x8, _arr_Y@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #392]
.L68:
  mov x0, #100
  str x0, [sp, #400]
.L69:
  ldr x1, [sp, #392]
  ldr x2, [sp, #400]
  mul x0, x1, x2
  str x0, [sp, #408]
.L70:
  ldr x1, [sp, #376]
  ldr x2, [sp, #408]
  add x0, x1, x2
  str x0, [sp, #416]
.L71:
  mov x0, #4
  str x0, [sp, #424]
.L72:
  ldr x1, [sp, #424]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_Y@PAGE
  add x8, x8, _arr_Y@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #432]
.L73:
  mov x0, #10
  str x0, [sp, #440]
.L74:
  ldr x1, [sp, #432]
  ldr x2, [sp, #440]
  mul x0, x1, x2
  str x0, [sp, #448]
.L75:
  ldr x1, [sp, #416]
  ldr x2, [sp, #448]
  add x0, x1, x2
  str x0, [sp, #456]
.L76:
  mov x0, #5
  str x0, [sp, #464]
.L77:
  ldr x1, [sp, #464]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_Y@PAGE
  add x8, x8, _arr_Y@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #472]
.L78:
  ldr x1, [sp, #456]
  ldr x2, [sp, #472]
  add x0, x1, x2
  str x0, [sp, #32]
.L79:
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
  // print a
  ldr x9, [sp, #16]
  sub sp, sp, #16
  adrp x8, .Lname_a@PAGE
  add x8, x8, .Lname_a@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print i
  ldr x9, [sp, #24]
  sub sp, sp, #16
  adrp x8, .Lname_i@PAGE
  add x8, x8, .Lname_i@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print r
  ldr x9, [sp, #32]
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
.Lname_n:
  .asciz "n"
.Lname_a:
  .asciz "a"
.Lname_i:
  .asciz "i"
.Lname_r:
  .asciz "r"

.section __DATA,__data
.global _arr_X
.align 3
_arr_X:
  .space 8192
.global _arr_Y
.align 3
_arr_Y:
  .space 8192
