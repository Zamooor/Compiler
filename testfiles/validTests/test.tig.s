global L3
L3:
mov rbx,3
mov r12, rbx
add r12,4
mov r13,3
mov r14, r13
add r14,4
add rax, r14
jmp L2
L2:
mov rdi, rax  
mov eax, 60  
syscall  
