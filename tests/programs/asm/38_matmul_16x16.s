.global _main
.align 2

_main:
  sub sp, sp, #432
  str x30, [sp, #424]
  str x29, [sp, #416]
  add x29, sp, #416

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
  mov x0, #16
  str x0, [sp, #8]
.L8:
  mov x0, #0
  str x0, [sp, #16]
.L9:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L42
.L10:
  mov x0, #0
  str x0, [sp, #24]
.L11:
  ldr x1, [sp, #24]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L39
.L12:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  mul x0, x1, x2
  str x0, [sp, #64]
.L13:
  ldr x1, [sp, #64]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #72]
.L14:
  mov x0, #3
  str x0, [sp, #80]
.L15:
  ldr x1, [sp, #16]
  ldr x2, [sp, #80]
  mul x0, x1, x2
  str x0, [sp, #88]
.L16:
  mov x0, #5
  str x0, [sp, #96]
.L17:
  ldr x1, [sp, #24]
  ldr x2, [sp, #96]
  mul x0, x1, x2
  str x0, [sp, #104]
.L18:
  ldr x1, [sp, #88]
  ldr x2, [sp, #104]
  add x0, x1, x2
  str x0, [sp, #112]
.L19:
  mov x0, #1
  str x0, [sp, #120]
.L20:
  ldr x1, [sp, #112]
  ldr x2, [sp, #120]
  add x0, x1, x2
  str x0, [sp, #128]
.L21:
  mov x0, #100
  str x0, [sp, #136]
.L22:
  ldr x2, [sp, #136]
  cbz x2, .Ldiv_by_zero
  ldr x1, [sp, #128]
  ldr x2, [sp, #136]
  sdiv x3, x1, x2
  msub x0, x3, x2, x1
  str x0, [sp, #144]
.L23:
  ldr x1, [sp, #72]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #144]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L24:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  mul x0, x1, x2
  str x0, [sp, #152]
.L25:
  ldr x1, [sp, #152]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #160]
.L26:
  mov x0, #7
  str x0, [sp, #168]
.L27:
  ldr x1, [sp, #16]
  ldr x2, [sp, #168]
  mul x0, x1, x2
  str x0, [sp, #176]
.L28:
  mov x0, #2
  str x0, [sp, #184]
.L29:
  ldr x1, [sp, #24]
  ldr x2, [sp, #184]
  mul x0, x1, x2
  str x0, [sp, #192]
.L30:
  ldr x1, [sp, #176]
  ldr x2, [sp, #192]
  add x0, x1, x2
  str x0, [sp, #200]
.L31:
  mov x0, #3
  str x0, [sp, #208]
.L32:
  ldr x1, [sp, #200]
  ldr x2, [sp, #208]
  add x0, x1, x2
  str x0, [sp, #216]
.L33:
  mov x0, #100
  str x0, [sp, #224]
.L34:
  ldr x2, [sp, #224]
  cbz x2, .Ldiv_by_zero
  ldr x1, [sp, #216]
  ldr x2, [sp, #224]
  sdiv x3, x1, x2
  msub x0, x3, x2, x1
  str x0, [sp, #232]
.L35:
  ldr x1, [sp, #160]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #232]
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L36:
  mov x0, #1
  str x0, [sp, #240]
.L37:
  ldr x1, [sp, #24]
  ldr x2, [sp, #240]
  add x0, x1, x2
  str x0, [sp, #24]
.L38:
  b .L11
.L39:
  mov x0, #1
  str x0, [sp, #248]
.L40:
  ldr x1, [sp, #16]
  ldr x2, [sp, #248]
  add x0, x1, x2
  str x0, [sp, #16]
.L41:
  b .L9
.L42:
  mov x0, #0
  str x0, [sp, #16]
.L43:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L69
.L44:
  mov x0, #0
  str x0, [sp, #24]
.L45:
  ldr x1, [sp, #24]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L66
.L46:
  mov x0, #0
  str x0, [sp, #40]
.L47:
  mov x0, #0
  str x0, [sp, #32]
.L48:
  ldr x1, [sp, #32]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L60
.L49:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  mul x0, x1, x2
  str x0, [sp, #256]
.L50:
  ldr x1, [sp, #256]
  ldr x2, [sp, #32]
  add x0, x1, x2
  str x0, [sp, #264]
.L51:
  ldr x1, [sp, #264]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #272]
.L52:
  ldr x1, [sp, #32]
  ldr x2, [sp, #8]
  mul x0, x1, x2
  str x0, [sp, #280]
.L53:
  ldr x1, [sp, #280]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #288]
.L54:
  ldr x1, [sp, #288]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_B@PAGE
  add x8, x8, _arr_B@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #296]
.L55:
  ldr x1, [sp, #272]
  ldr x2, [sp, #296]
  mul x0, x1, x2
  str x0, [sp, #304]
.L56:
  ldr x1, [sp, #40]
  ldr x2, [sp, #304]
  add x0, x1, x2
  str x0, [sp, #40]
.L57:
  mov x0, #1
  str x0, [sp, #312]
.L58:
  ldr x1, [sp, #32]
  ldr x2, [sp, #312]
  add x0, x1, x2
  str x0, [sp, #32]
.L59:
  b .L48
.L60:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  mul x0, x1, x2
  str x0, [sp, #320]
.L61:
  ldr x1, [sp, #320]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #328]
.L62:
  ldr x1, [sp, #328]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #40]
  adrp x8, _arr_C@PAGE
  add x8, x8, _arr_C@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L63:
  mov x0, #1
  str x0, [sp, #336]
.L64:
  ldr x1, [sp, #24]
  ldr x2, [sp, #336]
  add x0, x1, x2
  str x0, [sp, #24]
.L65:
  b .L45
.L66:
  mov x0, #1
  str x0, [sp, #344]
.L67:
  ldr x1, [sp, #16]
  ldr x2, [sp, #344]
  add x0, x1, x2
  str x0, [sp, #16]
.L68:
  b .L43
.L69:
  mov x0, #0
  str x0, [sp, #48]
.L70:
  mov x0, #0
  str x0, [sp, #56]
.L71:
  mov x0, #0
  str x0, [sp, #16]
.L72:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L89
.L73:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  mul x0, x1, x2
  str x0, [sp, #352]
.L74:
  ldr x1, [sp, #352]
  ldr x2, [sp, #16]
  add x0, x1, x2
  str x0, [sp, #360]
.L75:
  ldr x1, [sp, #360]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_C@PAGE
  add x8, x8, _arr_C@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #368]
.L76:
  ldr x1, [sp, #48]
  ldr x2, [sp, #368]
  add x0, x1, x2
  str x0, [sp, #48]
.L77:
  mov x0, #0
  str x0, [sp, #24]
.L78:
  ldr x1, [sp, #24]
  ldr x2, [sp, #8]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L86
.L79:
  ldr x1, [sp, #16]
  ldr x2, [sp, #8]
  mul x0, x1, x2
  str x0, [sp, #376]
.L80:
  ldr x1, [sp, #376]
  ldr x2, [sp, #24]
  add x0, x1, x2
  str x0, [sp, #384]
.L81:
  ldr x1, [sp, #384]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_C@PAGE
  add x8, x8, _arr_C@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #392]
.L82:
  ldr x1, [sp, #56]
  ldr x2, [sp, #392]
  add x0, x1, x2
  str x0, [sp, #56]
.L83:
  mov x0, #1
  str x0, [sp, #400]
.L84:
  ldr x1, [sp, #24]
  ldr x2, [sp, #400]
  add x0, x1, x2
  str x0, [sp, #24]
.L85:
  b .L78
.L86:
  mov x0, #1
  str x0, [sp, #408]
.L87:
  ldr x1, [sp, #16]
  ldr x2, [sp, #408]
  add x0, x1, x2
  str x0, [sp, #16]
.L88:
  b .L72
.L89:
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
  // print trace
  ldr x9, [sp, #48]
  sub sp, sp, #16
  adrp x8, .Lname_trace@PAGE
  add x8, x8, .Lname_trace@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16
  // print checksum
  ldr x9, [sp, #56]
  sub sp, sp, #16
  adrp x8, .Lname_checksum@PAGE
  add x8, x8, .Lname_checksum@PAGEOFF
  str x8, [sp]
  str x9, [sp, #8]
  adrp x0, .Lfmt@PAGE
  add x0, x0, .Lfmt@PAGEOFF
  bl _printf
  add sp, sp, #16

  // Exit with code 0
  mov x0, #0
  ldr x29, [sp, #416]
  ldr x30, [sp, #424]
  add sp, sp, #432
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
.Lname_trace:
  .asciz "trace"
.Lname_checksum:
  .asciz "checksum"

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
