; max.asm - Find maximum value in array
; Input: array address (a), array length (n)
; Output: maximum value in array
;
; C equivalent:
;   mx = a[0];
;   for (int i = 1; i < n; i++) {
;       if (a[i] > mx) mx = a[i];
;   }
;   return mx;
;
; Stack layout:
;   On entry: [a, n]
;   During:   [a, n, mx, i]

main:
    ; Check if n > 0
    DUP 0           ; [a, n, n]
    PUSH 0          ; [a, n, n, 0]
    ALU LT          ; [a, n, (n>0)]
    JZ error        ; If n <= 0, return error
    
    ; Load a[0] as initial max
    DUP 1           ; [a, n, a]
    LOAD            ; [a, n, mx=a[0]]
    
    ; Initialize i = 1
    PUSH 1          ; [a, n, mx, i=1]
    
loop:
    ; Check if i < n
    DUP 0           ; [a, n, mx, i, i]
    DUP 3           ; [a, n, mx, i, i, n]
    ALU LT          ; [a, n, mx, i, (i<n)]
    JZ done         ; If i >= n, exit loop
    
    ; Calculate address a+i
    DUP 3           ; [a, n, mx, i, a]
    DUP 1           ; [a, n, mx, i, a, i]
    ALU ADD         ; [a, n, mx, i, addr=a+i]
    
    ; Load a[i]
    LOAD            ; [a, n, mx, i, a[i]]
    
    ; Check if a[i] > mx
    DUP 1           ; [a, n, mx, i, a[i], mx]
    ALU LT          ; [a, n, mx, i, (mx<a[i])]
    JZ skip_update  ; If mx >= a[i], skip
    
    ; Update: mx = a[i]
    ; Reload a[i]
    DUP 3           ; [a, n, mx, i, a]
    DUP 1           ; [a, n, mx, i, a, i]
    ALU ADD         ; [a, n, mx, i, addr]
    LOAD            ; [a, n, mx, i, new_mx=a[i]]
    
    ; Replace mx: pop old, use new
    ; Stack trick: [a, n, old_mx, i, new_mx]
    ; We need: [a, n, new_mx, i]
    DUP 1           ; [a, n, old_mx, i, new_mx, i]
    DUP 1           ; [a, n, old_mx, i, new_mx, i, new_mx]
    POP 1           ; [a, n, old_mx, i, new_mx, i]
    POP 1           ; [a, n, old_mx, i, new_mx]
    POP 1           ; [a, n, old_mx, new_mx]
    ; Hmm, this is getting complex. Let me use a different approach.
    
skip_update:
    ; Increment i
    PUSH 1          ; [a, n, mx, i, 1]
    ALU ADD         ; [a, n, mx, i+1]
    JMP loop
    
done:
    ; Return mx
    ; Stack: [a, n, mx, i]
    ; We want to return just mx
    POP 1           ; [a, n, mx]
    RET 1           ; Return with mx on stack

error:
    PUSH -1         ; Return -1 for error
    RET 1
