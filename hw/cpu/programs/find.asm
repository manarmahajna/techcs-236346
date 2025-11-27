; find.asm - Search for value in array
; Input: array address (a), array length (n), search value (v)
; Output: index where v is found, or n if not found
;
; C equivalent:
;   for (at = 0; at < n; at++) {
;       if (a[at] == v) break;
;   }
;   return at;
;
; Memory layout:
;   0x1000: a (array address)
;   0x1001: n (array length)
;   0x1002: v (search value)
;   0x1003: at (loop counter / result)

main:
    ; Store inputs: [a, n, v]
    PUSH 0x1002
    STOR            ; Store v, [a, n]
    PUSH 0x1001
    STOR            ; Store n, [a]
    PUSH 0x1000
    STOR            ; Store a, []
    
    ; at = 0
    PUSH 0
    PUSH 0x1003
    STOR            ; at = 0
    
loop:
    ; if (at >= n) goto done
    PUSH 0x1003
    LOAD            ; Load at
    PUSH 0x1001
    LOAD            ; Load n
    ALU LT          ; at < n?
    JZ done         ; If at >= n, not found
    
    ; Load a[at]
    PUSH 0x1000
    LOAD            ; Load a
    PUSH 0x1003
    LOAD            ; Load at
    ALU ADD         ; a + at
    LOAD            ; a[at]
    
    ; Compare a[at] with v
    PUSH 0x1002
    LOAD            ; Load v
    ALU SUB         ; a[at] - v
    JZ found        ; If a[at] == v, found!
    
    ; at++
    PUSH 0x1003
    LOAD            ; Load at
    PUSH 1
    ALU ADD         ; at + 1
    PUSH 0x1003
    STOR            ; Store at+1
    JMP loop
    
found:
done:
    ; Return at
    PUSH 0x1003
    LOAD            ; Load at
    RET 1
