global _start

section .data
    type_size: db 1,8,16,8,8

section .text
_start:
    ; syscalls
    %define sys_brk         12
    %define sys_write       1
    %define sys_exit        60

    ; registers
    ;; pointer to the start of the available region of heap
    %define heap_start       r15
    ;; pointer to end of the heap
    %define heap_end        r14
    ;; pointer to the last returned value
    %define retval          r13

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
    %define application_t   4

    ; exit with given code
    %macro exit 1
        mov rdi, %1
        mov rax, sys_exit
        syscall
    %endmacro

    ; ensure at least %1 bytes of memory available
    %macro ensuremem 1
        mov rdx, heap_start
        add rdx, %1
        cmp rdx, heap_end
        jle alloc_until
        ret
    %endmacro

    jmp main

; allocate one page on heap
alloc_page:
    mov rax, sys_brk
    mov rdi, page
    add rdi, heap_end
    syscall
    ret

; allocate pages until heap_end is greater than rdx
alloc_until:
    jmp alloc_page
    cmp rdx, heap_end
    jle alloc_until
    ret

generic_error:
    exit 1

main:

    ; set base pointer to current stack location
    mov rbp, rsp

    ; start generated instructions
    ; --- generated instructions ---
    ; end generated instructions

    ; print result and exiting

    ;; set rsi to actual pointer data (drop type info)
    mov rsi, retval
    and rsi, bottom_3_zero

    ;; get bottom 3 bits of retval
    xor rdx, rdx
    ;; retval is now just bottom 3 bits (type info)
    and retval, bottom_3_set
    mov byte dl, [type_size + retval]

    mov rax, sys_write
    ; set fd to 1 (stdout)
    mov rdi, 1
    syscall

    exit 0
