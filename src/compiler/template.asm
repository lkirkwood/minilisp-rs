global _start

section .data
    ; type size array
    type_size:              db 1,8,16,8,8
    ; temporary value store
    tmp_val:                resb 8

section .text
_start:
    ; syscalls
    %define sys_brk         12
    %define sys_write       1
    %define sys_exit        60

    ; registers
    ;; pointer to the start of the available region of heap
    %define heap_start      r15
    ;; pointer to end of the heap
    %define heap_end        r14
    ;; the returned value
    %define retval          r13
    ;; type of retval
    %define rettype         r12
    ;; lambda context heap base
    %define lambda_ctx      r11

    ; page size (4KB)
    %define page            4096

    ; bottom 3 bits set
    %define bottom_3_set    7
    ; all bits set except for bottom 3
    %define bottom_3_zero   18446744073709551608

    ; value types that can occupy [type]
    %define null_t          0
    %define num_t           1
    %define cons_t          2
    %define lambda_t        3

    ; exit with given code
    %macro exit 1
        mov rdi, %1
        mov rax, sys_exit
        syscall
    %endmacro

    ; set up heap
    mov rax, sys_brk
    xor rdi, rdi
    syscall
    mov heap_start, rax
    mov heap_end, rax

    jmp main

; checks there is at least rdx bytes left on the heap
; allocates pages until there is
ensure_mem:
    add rdx, heap_start
.check_size:
    push rdx
    cmp rdx, heap_end
    ja  .alloc_page
    pop rdx
    ret
.alloc_page:
    mov rdi, heap_end
    add rdi, page
    mov rax, sys_brk
    syscall
    mov heap_end, rax
    pop rdx
    jmp .check_size

generic_error:
    exit 1

main:

    ; set base pointer to current stack location
    mov rbp, rsp

    ; start generated instructions
    ; --- generated instructions ---
    ; end generated instructions

    ; print result and exiting

    push retval
    mov rsi, rsp
    xor rdx, rdx
    movzx rdx, byte [type_size + rettype]

    mov rax, sys_write
    ; set fd to 1 (stdout)
    mov rdi, 1
    syscall

    exit 0
