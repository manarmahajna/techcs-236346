# StASM Assembly Programs

Assembly language programs for the StaM (Stack Machine) CPU.

## Programs

### max.asm / max_simple.asm
Find the maximum value in an array.

**Inputs:**
- `a`: Array base address
- `n`: Array length

**Output:**
- Maximum value in array, or -1 on error

**Algorithm:** Linear scan with comparison

**Usage:**
```python
result = run_program("max_simple.asm", 
                     memory={0x2000: [5, 2, 9, 1, 7]},
                     inputs=[0x2000, 5])
# result = 9
```

### find.asm
Search for a value in an array.

**Inputs:**
- `a`: Array base address
- `n`: Array length
- `v`: Value to search for

**Output:**
- Index where value is found, or `n` if not found

**Algorithm:** Linear search

**Usage:**
```python
result = run_program("find.asm",
                     memory={0x2000: [10, 20, 30, 40, 50]},
                     inputs=[0x2000, 5, 30])
# result = 2 (index of value 30)
```

## Testing

Run the test suite:
```bash
python3 test_programs.py
```

This will test both programs with multiple test cases including:
- Edge cases (empty arrays, single elements)
- Normal cases (various array sizes)
- Error cases (value not found, etc.)

## Memory Layout

Programs use memory locations:
- `0x1000`: Variable storage area
- `0x1001-0x1003`: Temporary variables
- `0x2000+`: Test data arrays

## StASM Syntax

```assembly
; Comments
label:
    PUSH value      ; Push constant
    POP 1           ; Pop items
    DUP 0           ; Duplicate
    ALU ADD         ; Arithmetic
    LOAD            ; Load from memory
    STOR            ; Store to memory
    JMP label       ; Jump
    JZ label        ; Conditional
    RET 1           ; Return with value
```

## Development Notes

### Stack vs. Memory Variables

Two approaches:

**Stack-based** (max.asm):
- Keeps values on stack
- More complex manipulation
- Fewer memory accesses

**Memory-based** (max_simple.asm, find.asm):
- Uses memory for variables
- Simpler logic
- More memory accesses
- Easier to understand

### Common Patterns

**Loop:**
```assembly
loop:
    ; Check condition
    ; ...
    JZ done
    ; Loop body
    ; ...
    ; Update counter
    JMP loop
done:
```

**Conditional:**
```assembly
    ; Compute condition
    ALU LT          ; Or other comparison
    JZ else_label
    ; Then branch
    JMP endif
else_label:
    ; Else branch
endif:
```

## See Also

- `../STAM_ARCHITECTURE.md` - CPU specification
- `../instruction_set.py` - Instruction encoding
- `../assembler.py` - Assembler
