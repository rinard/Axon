.global _main
.align 2

_main:
  sub sp, sp, #448
  str x30, [sp, #440]
  str x29, [sp, #432]
  add x29, sp, #432

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
  mov x0, #5
  str x0, [sp, #8]
.L6:
  mov x0, #0
  str x0, [sp, #48]
.L7:
  mov x0, #5
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
  mov x0, #3
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
  mov x0, #1
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
  mov x0, #2
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
  mov x0, #0
  str x0, [sp, #16]
.L22:
  mov x0, #1
  str x0, [sp, #128]
.L23:
  ldr x1, [sp, #8]
  ldr x2, [sp, #128]
  sub x0, x1, x2
  str x0, [sp, #136]
.L24:
  ldr x1, [sp, #16]
  ldr x2, [sp, #136]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L51
.L25:
  mov x0, #0
  str x0, [sp, #24]
.L26:
  mov x0, #1
  str x0, [sp, #144]
.L27:
  ldr x1, [sp, #8]
  ldr x2, [sp, #144]
  sub x0, x1, x2
  str x0, [sp, #152]
.L28:
  ldr x1, [sp, #152]
  ldr x2, [sp, #16]
  sub x0, x1, x2
  str x0, [sp, #160]
.L29:
  ldr x1, [sp, #24]
  ldr x2, [sp, #160]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L48
.L30:
  mov x0, #1
  str x0, [sp, #168]
.L31:
  ldr x1, [sp, #24]
  ldr x2, [sp, #168]
  add x0, x1, x2
  str x0, [sp, #176]
.L32:
  ldr x1, [sp, #176]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #184]
.L33:
  ldr x1, [sp, #24]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #192]
.L34:
  ldr x1, [sp, #184]
  ldr x2, [sp, #192]
  cmp x1, x2
  cset w0, lt
  cbnz w0, .L36
.L35:
  b .L45
.L36:
  ldr x1, [sp, #24]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #200]
.L37:
  ldr x0, [sp, #200]
  str x0, [sp, #32]
.L38:
  mov x0, #1
  str x0, [sp, #208]
.L39:
  ldr x1, [sp, #24]
  ldr x2, [sp, #208]
  add x0, x1, x2
  str x0, [sp, #216]
.L40:
  ldr x1, [sp, #216]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #224]
.L41:
  ldr x1, [sp, #24]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #224]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L42:
  mov x0, #1
  str x0, [sp, #232]
.L43:
  ldr x1, [sp, #24]
  ldr x2, [sp, #232]
  add x0, x1, x2
  str x0, [sp, #240]
.L44:
  ldr x1, [sp, #240]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #32]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L45:
  mov x0, #1
  str x0, [sp, #248]
.L46:
  ldr x1, [sp, #24]
  ldr x2, [sp, #248]
  add x0, x1, x2
  str x0, [sp, #24]
.L47:
  b .L26
.L48:
  mov x0, #1
  str x0, [sp, #256]
.L49:
  ldr x1, [sp, #16]
  ldr x2, [sp, #256]
  add x0, x1, x2
  str x0, [sp, #16]
.L50:
  b .L22
.L51:
  mov x0, #0
  str x0, [sp, #264]
.L52:
  ldr x1, [sp, #264]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #272]
.L53:
  mov x0, #10000
  str x0, [sp, #280]
.L54:
  ldr x1, [sp, #272]
  ldr x2, [sp, #280]
  mul x0, x1, x2
  str x0, [sp, #288]
.L55:
  mov x0, #1
  str x0, [sp, #296]
.L56:
  ldr x1, [sp, #296]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #304]
.L57:
  mov x0, #1000
  str x0, [sp, #312]
.L58:
  ldr x1, [sp, #304]
  ldr x2, [sp, #312]
  mul x0, x1, x2
  str x0, [sp, #320]
.L59:
  ldr x1, [sp, #288]
  ldr x2, [sp, #320]
  add x0, x1, x2
  str x0, [sp, #328]
.L60:
  mov x0, #2
  str x0, [sp, #336]
.L61:
  ldr x1, [sp, #336]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #344]
.L62:
  mov x0, #100
  str x0, [sp, #352]
.L63:
  ldr x1, [sp, #344]
  ldr x2, [sp, #352]
  mul x0, x1, x2
  str x0, [sp, #360]
.L64:
  ldr x1, [sp, #328]
  ldr x2, [sp, #360]
  add x0, x1, x2
  str x0, [sp, #368]
.L65:
  mov x0, #3
  str x0, [sp, #376]
.L66:
  ldr x1, [sp, #376]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #384]
.L67:
  mov x0, #10
  str x0, [sp, #392]
.L68:
  ldr x1, [sp, #384]
  ldr x2, [sp, #392]
  mul x0, x1, x2
  str x0, [sp, #400]
.L69:
  ldr x1, [sp, #368]
  ldr x2, [sp, #400]
  add x0, x1, x2
  str x0, [sp, #408]
.L70:
  mov x0, #4
  str x0, [sp, #416]
.L71:
  ldr x1, [sp, #416]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #424]
.L72:
  ldr x1, [sp, #408]
  ldr x2, [sp, #424]
  add x0, x1, x2
  str x0, [sp, #40]
.L73:
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
  ldr x29, [sp, #432]
  ldr x30, [sp, #440]
  add sp, sp, #448
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
