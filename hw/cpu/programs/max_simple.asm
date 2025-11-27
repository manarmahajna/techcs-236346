; max_simple.asm - Simplified maximum finder
; Uses memory locations for variables to avoid complex stack manipulation
;
; Memory layout:
;   0x1000: a (array address)
;   0x1001: n (array length)
;   0x1002: mx (current maximum)
;   0x1003: i (loop counter)

main:
    ; Store inputs to memory
    ; Assume a and n are on stack: [a, n]
    PUSH 0x1001     ; [a, n, addr_n]
    STOR            ; Store n at 0x1001, [a]
    PUSH 0x1000     ; [a, addr_a]
    STOR            ; Store a at 0x1000, []
    
    ; Check n > 0
    PUSH 0x1001
    LOAD            ; Load n
    PUSH 0
    ALU LT          ; n > 0?
    JZ error
    
    ; mx = a[0]
    PUSH 0x1000
    LOAD            ; Load a
    LOAD            ; Load a[0]
    PUSH 0x1002
    STOR            ; mx = a[0]
    
    ; i = 1
    PUSH 1
    PUSH 0x1003
    STOR            ; i = 1
    
loop:
    ; if (i >= n) goto done
    PUSH 0x1003
    LOAD            ; Load i
    PUSH 0x1001
    LOAD            ; Load n
    ALU LT          ; i < n?
    JZ done
    
    ; Load a[i]
    PUSH 0x1000
    LOAD            ; Load a
    PUSH 0x1003
    LOAD            ; Load i
    ALU ADD         ; a + i
    LOAD            ; a[i]
    
    ; if (a[i] > mx) mx = a[i]
    DUP 0           ; [a[i], a[i]]
    PUSH 0x1002
    LOAD            ; [a[i], a[i], mx]
    ALU LT          ; [a[i], (mx < a[i])]
    JZ no_update
    
    ; mx = a[i]
    PUSH 0x1002
    STOR            ; Store a[i] to mx
    JMP inc_i
    
no_update:
    POP 1           ; Remove a[i]
    
inc_i:
    ; i++
    PUSH 0x1003
    LOAD            ; Load i
    PUSH 1
    ALU ADD         ; i + 1
    PUSH 0x1003
    STOR            ; Store i+1
    JMP loop
    
done:
    ; Return mx
    PUSH 0x1002
    LOAD            ; Load mx
    RET 1
    
error:
    PUSH -1
    RET 1
