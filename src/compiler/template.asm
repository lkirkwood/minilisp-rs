global _start

section .data

print_jump_table:
    dq print_null
    dq print_num
    dq print_cons
    dq print_lambda

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

    ; write one byte from the argument
    %macro write 2
        push %1
        mov rsi, rsp
        mov rdx, %2
        mov rax, sys_write
        mov rdi, 1
        syscall
        pop rax
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

print_retval:
    jmp [print_jump_table + rettype*8]

print_null:
    write 0x8588E2, 3
    ret

print_num:
    ;; divide by 10
    ;; print remainder
    ;; repeat with quotient
    mov rax, retval
    mov rbx, 10
    xor r10, r10
.div_loop:
    xor rdx, rdx
    div rbx
    push rdx
    inc r10
    cmp rax, 0
    jne .div_loop
.write_loop:
    pop rax
    add rax, '0'
    write rax, 1
    dec r10
    cmp r10, 0
    jne .write_loop
    ret

print_lambda:
    write 0x0028, 1             ; left paren
    write 0xBBCE, 2             ; λ as big endian utf8
    write 0x0029, 1             ; right paren
    ret

print_cons:
    write 0x0028, 1             ; left paren
    write 0xB788E2, 3           ; ∷ as big endian utf8
    write 0x0020, 1             ; space
    push retval
.print_car:
    mov rdi, retval
    mov retval, [rdi]
    mov rettype, [rdi + 8]
    call print_retval
    write 0x0020, 1             ; space
.print_cdr:
    pop rdi
    add rdi, 16
    mov retval, [rdi]
    mov rettype, [rdi + 8]
    call print_retval
    write 0x0029, 1             ; right paren
    ret

main:
    ; set base pointer to current stack location
    mov rbp, rsp

    ; start generated instructions
    ; --- generated instructions ---
    ; end generated instructions

    ; print result and exiting

    call print_retval
    exit 0
