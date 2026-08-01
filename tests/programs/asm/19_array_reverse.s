.global _main
.align 2

_main:
  sub sp, sp, #352
  str x30, [sp, #344]
  str x29, [sp, #336]
  add x29, sp, #336

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
  mov x0, #5
  str x0, [sp, #8]
.L5:
  mov x0, #0
  str x0, [sp, #40]
.L6:
  mov x0, #1
  str x0, [sp, #48]
.L7:
  ldr x1, [sp, #40]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #48]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L8:
  mov x0, #1
  str x0, [sp, #56]
.L9:
  mov x0, #2
  str x0, [sp, #64]
.L10:
  ldr x1, [sp, #56]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #64]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L11:
  mov x0, #2
  str x0, [sp, #72]
.L12:
  mov x0, #3
  str x0, [sp, #80]
.L13:
  ldr x1, [sp, #72]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #80]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L14:
  mov x0, #3
  str x0, [sp, #88]
.L15:
  mov x0, #4
  str x0, [sp, #96]
.L16:
  ldr x1, [sp, #88]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #96]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L17:
  mov x0, #4
  str x0, [sp, #104]
.L18:
  mov x0, #5
  str x0, [sp, #112]
.L19:
  ldr x1, [sp, #104]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #112]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L20:
  mov x0, #0
  str x0, [sp, #16]
.L21:
  mov x0, #1
  str x0, [sp, #120]
.L22:
  ldr x1, [sp, #8]
  ldr x2, [sp, #120]
  sub x0, x1, x2
  str x0, [sp, #24]
.L23:
  ldr x1, [sp, #16]
  ldr x2, [sp, #24]
  cmp x1, x2
  cset w0, lt
  eor w0, w0, #1
  cbnz w0, .L34
.L24:
  ldr x1, [sp, #16]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #128]
.L25:
  ldr x0, [sp, #128]
  str x0, [sp, #32]
.L26:
  ldr x1, [sp, #24]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #136]
.L27:
  ldr x1, [sp, #16]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #136]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L28:
  ldr x1, [sp, #24]
  cmp x1, #1024
  b.hs .Lbounds_err
  ldr x2, [sp, #32]
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  str x2, [x8, x1, lsl #3]
.L29:
  mov x0, #1
  str x0, [sp, #144]
.L30:
  ldr x1, [sp, #16]
  ldr x2, [sp, #144]
  add x0, x1, x2
  str x0, [sp, #16]
.L31:
  mov x0, #1
  str x0, [sp, #152]
.L32:
  ldr x1, [sp, #24]
  ldr x2, [sp, #152]
  sub x0, x1, x2
  str x0, [sp, #24]
.L33:
  b .L23
.L34:
  mov x0, #0
  str x0, [sp, #160]
.L35:
  ldr x1, [sp, #160]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #168]
.L36:
  mov x0, #10000
  str x0, [sp, #176]
.L37:
  ldr x1, [sp, #168]
  ldr x2, [sp, #176]
  mul x0, x1, x2
  str x0, [sp, #184]
.L38:
  mov x0, #1
  str x0, [sp, #192]
.L39:
  ldr x1, [sp, #192]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #200]
.L40:
  mov x0, #1000
  str x0, [sp, #208]
.L41:
  ldr x1, [sp, #200]
  ldr x2, [sp, #208]
  mul x0, x1, x2
  str x0, [sp, #216]
.L42:
  ldr x1, [sp, #184]
  ldr x2, [sp, #216]
  add x0, x1, x2
  str x0, [sp, #224]
.L43:
  mov x0, #2
  str x0, [sp, #232]
.L44:
  ldr x1, [sp, #232]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #240]
.L45:
  mov x0, #100
  str x0, [sp, #248]
.L46:
  ldr x1, [sp, #240]
  ldr x2, [sp, #248]
  mul x0, x1, x2
  str x0, [sp, #256]
.L47:
  ldr x1, [sp, #224]
  ldr x2, [sp, #256]
  add x0, x1, x2
  str x0, [sp, #264]
.L48:
  mov x0, #3
  str x0, [sp, #272]
.L49:
  ldr x1, [sp, #272]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #280]
.L50:
  mov x0, #10
  str x0, [sp, #288]
.L51:
  ldr x1, [sp, #280]
  ldr x2, [sp, #288]
  mul x0, x1, x2
  str x0, [sp, #296]
.L52:
  ldr x1, [sp, #264]
  ldr x2, [sp, #296]
  add x0, x1, x2
  str x0, [sp, #304]
.L53:
  mov x0, #4
  str x0, [sp, #312]
.L54:
  ldr x1, [sp, #312]
  cmp x1, #1024
  b.hs .Lbounds_err
  adrp x8, _arr_A@PAGE
  add x8, x8, _arr_A@PAGEOFF
  ldr x0, [x8, x1, lsl #3]
  str x0, [sp, #320]
.L55:
  ldr x1, [sp, #304]
  ldr x2, [sp, #320]
  add x0, x1, x2
  str x0, [sp, #32]
.L56:
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

  // Exit with code 0
  mov x0, #0
  ldr x29, [sp, #336]
  ldr x30, [sp, #344]
  add sp, sp, #352
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

.section __DATA,__data
.global _arr_A
.align 3
_arr_A:
  .space 8192
