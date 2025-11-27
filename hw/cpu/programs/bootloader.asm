; bootloader.asm - Boot loader for StaM CPU
; 
; Purpose: Load program from GPIO into RAM at kernel address (0xe800)
;          then jump to the loaded code
;
; GPIO Protocol:
;   - First word: Program length (number of words to load)
;   - Following words: Program code
;
; Memory Map:
;   0xc000: GPIO_IN_LO  (read input low 16 bits)
;   0xc001: GPIO_IN_HI  (read input high 16 bits)
;   0xe800: Kernel start address (where program is loaded)
;   0xffff: Top of stack
;
; Algorithm:
;   1. Read program length from GPIO
;   2. For each word:
;      a. Read word from GPIO
;      b. Write to RAM at kernel_addr + offset
;   3. Set up stack pointer
;   4. Jump to kernel address

main:
    ; Initialize variables in memory
    ; 0x1000: kernel_addr = 0xe800
    ; 0x1001: current_offset = 0
    ; 0x1002: program_length
    ; 0x1003: GPIO_IN_LO address = 0xc000
    
    ; Set kernel_addr = 0xe800
    PUSH 0xe800
    PUSH 0x1000
    STOR
    
    ; Set GPIO_IN_LO = 0xc000
    PUSH 0xc000
    PUSH 0x1003
    STOR
    
    ; Read program length
    ; Wait for GPIO ready (poll until data available)
    PUSH 0xc001         ; GPIO_IN_HI address
    LOAD                ; Read GPIO_IN_HI (status)
    JZ wait_length      ; If zero, wait
    
    ; Read length
    PUSH 0xc000
    LOAD                ; Read program length from GPIO_IN_LO
    PUSH 0x1002
    STOR                ; Store program_length
    
    ; Initialize offset = 0
    PUSH 0
    PUSH 0x1001
    STOR
    
load_loop:
    ; Check if offset < program_length
    PUSH 0x1001
    LOAD                ; Load offset
    PUSH 0x1002
    LOAD                ; Load program_length
    ALU LT              ; offset < length?
    JZ boot_done        ; If not, we're done loading
    
    ; Wait for next word
wait_word:
    PUSH 0xc001
    LOAD                ; Check GPIO_IN_HI
    JZ wait_word        ; Wait until data ready
    
    ; Read word from GPIO
    PUSH 0xc000
    LOAD                ; Read word
    
    ; Calculate destination address: kernel_addr + offset
    PUSH 0x1000
    LOAD                ; Load kernel_addr
    PUSH 0x1001
    LOAD                ; Load offset
    ALU ADD             ; kernel_addr + offset
    
    ; Store word at destination
    STOR                ; mem[kernel_addr + offset] = word
    
    ; Increment offset
    PUSH 0x1001
    LOAD
    PUSH 1
    ALU ADD             ; offset + 1
    PUSH 0x1001
    STOR                ; Store new offset
    
    JMP load_loop
    
wait_length:
    ; Keep polling until length arrives
    PUSH 0xc001
    LOAD
    JZ wait_length
    JMP main
    
boot_done:
    ; Set up stack pointer at top of memory
    ; (In actual implementation, sp would be a register)
    ; For now, we'll just jump to the kernel
    
    ; Jump to kernel address (0xe800)
    PUSH 0xe800
    PUSH 0              ; Dummy return value (won't return)
    RET 0               ; Indirect jump to kernel
