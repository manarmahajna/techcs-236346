# StaM (Stack Machine) CPU Architecture

**Based on**: [03-cpu-machine.pdf](file://03-cpu-machine (1).pdf)

## Overview

StaM is a **stack-based CPU** with 16-bit words and a simple instruction set designed for ease of verification.

### Key Features
- **16-bit word-addressable RAM**
- **Stack-based architecture** (no general-purpose registers)
- **4-bit opcode + 16-bit argument** instruction format
- **Memory-mapped I/O** (GPIO, Video)

---

## Instruction Set

### Instruction Format
```
┌──────────┬─────────────────┐
│  opcode  │    argument     │
│  4 bits  │    16 bits      │
└──────────┴─────────────────┘
```

### Stack Instructions

| Instruction | Arg | Description |
|------------|-----|-------------|
| **PUSH** | val | Push constant value onto stack |
| **POP** | cnt | Pop cnt items (1 or 2) from stack |
| **DUP** | ofs | Duplicate stack element at offset ofs |

**Stack Notation:**
- `r₀` = top of stack
- `r₁` = second item on stack
- `r₂` = third item on stack, etc.

### ALU Instructions

| Instruction | Operation | Description |
|------------|-----------|-------------|
| **ALU ADD** | r₁ + r₀ | Pop 2, push sum |
| **ALU SUB** | r₁ - r₀ | Pop 2, push difference |
| **ALU MUL** | r₁ × r₀ | Pop 2, push product |
| **ALU NEG** | -r₀ | Pop 1, push negation |
| **ALU AND** | r₁ & r₀ | Pop 2, push bitwise AND |
| **ALU OR** | r₁ \| r₀ | Pop 2, push bitwise OR |
| **ALU NOT** | ~r₀ | Pop 1, push bitwise NOT |
| **ALU SHL** | r₁ << r₀ | Pop 2, push left shift |
| **ALU SHR** | r₁ >> r₀ | Pop 2, push right shift |
| **ALU LT** | r₁ < r₀ | Pop 2, push 1 if true, else 0 |

**Note**: Binary operations pop two values, use second-to-top as left operand.

### Memory Instructions

| Instruction | Arg | Description |
|------------|-----|-------------|
| **LOAD** | — | Pop address r₀, push mem[r₀] |
| **STOR** | — | Pop value r₀ and address r₁, store mem[r₁] := r₀ |

### Control Flow Instructions

| Instruction | Arg | Description |
|------------|-----|-------------|
| **JMP** | addr | Unconditional jump to addr |
| **JZ** | addr | Pop r₀, jump to addr if r₀ = 0 |
| **JNZ** | addr | Pop r₀, jump to addr if r₀ ≠ 0 |
| **RET** | flag | Pop r₀, jump to r₀; if flag=1, push r₁ |

**RET Semantics:**
- Used for function returns
- `RET 0`: Simple return (indirect jump to r₀)
- `RET 1`: Return with value (jump to r₀, push r₁)

---

## Memory Map

```
0x0000 ─────────┐
                │  Program Code
0x???? ─────────┤
                │  Stack (grows upward)
0x???? ─────────┤
                │  Heap / Data
0xa000 ─────────┤
                │  Video Memory
                │  (16 words × 16 rows = 256 words)
0xa100 ─────────┤
                │  (unused)
0xc000 ─────────┤
                │  GPIO
                │  +0x0: gpio_in[15:0]
                │  +0x1: gpio_in[31:16]
                │  +0x2: gpio_out[15:0]
                │  +0x3: gpio_out[31:16]
0xc004 ─────────┤
                │  (unused)
0xffff ─────────┘
```

---

## Peripherals

### GPIO Adapter (0xc000)

**Registers:**
- `GPIO_IN_LO` (0xc000): Read-only, input bits [15:0]
- `GPIO_IN_HI` (0xc001): Read-only, input bits [31:16]
- `GPIO_OUT_LO` (0xc002): Write, output bits [15:0]
- `GPIO_OUT_HI` (0xc003): Write, output bits [31:16]

**Implementation**: See `periph.py`

### Video Adapter (0xa000)

**Memory Layout:**
- Base: 0xa000
- Size: 256 words (16 columns × 16 rows)
- Address: `base + (y * 16) + x`
- Auto-scanning display

**Implementation**: See `periph.py`

---

## Assembly Language (StASM)

### Syntax

```assembly
; Comments start with semicolon

label:              ; Label definition
    PUSH 42         ; Push constant
    PUSH value      ; Push named constant/label
    POP 1           ; Pop one item
    DUP 0           ; Duplicate top (r₀)
    
    ALU ADD         ; Add r₁ + r₀
    ALU SUB         ; Subtract r₁ - r₀
    
    LOAD            ; Load from memory
    STOR            ; Store to memory
    
    JMP label       ; Jump to label
    JZ label        ; Conditional jump
    JNZ label       ; Conditional jump
    
    RET 0           ; Return
    RET 1           ; Return with value
```

### Example: Add Two Numbers

```assembly
; Compute a + b
main:
    PUSH 10         ; Push a
    PUSH 20         ; Push b
    ALU ADD         ; Add them
    ; Result (30) now on top of stack
    RET 1           ; Return result
```

---

## Programming Examples

### Task 1: Find Maximum in Array

**C Code:**
```c
// input: a, n
mx = a[0];
for (int i = 1; i < n; i++) {
    if (a[i] > mx) mx = a[i];
}
return mx;
```

**StASM Implementation**: See `programs/max.asm`

### Task 2: Search for Value in Array

**C Code:**
```c
// input: a, n, v
for (at = 0; at < n; at++) {
    if (a[at] == v) break;
}
return at;
```

**StASM Implementation**: See `programs/find.asm`

---

## Testing

Use Python to test assembly programs:

```python
from assembler import assemble
from simulation import run_program

# Assemble program
machine_code = assemble("max.asm")

# Run with test data
result = run_program(machine_code, 
                    memory={0x100: [5, 2, 9, 1, 7]},
                    args=[0x100, 5])  # array addr, length

assert result == 9  # Maximum value
```

---

## Files

- `instruction_set.py` - Instruction encoding/decoding
- `assembler.py` - StASM → Machine code
- `periph.py` - GPIO and Video adapters
- `simulate/` - CPU simulation (Python, C, Verilog)

---

## Next Steps

1. ✓ Understand instruction set
2. Write assembly programs (max, find)
3. Create test suite
4. Run simulations
5. Verify correctness formally

---

**See Also:**
- [03-cpu-machine.pdf](file://03-cpu-machine (1).pdf) - Full specification
- `cpu.ipynb` - CPU design notebook
- `stack-simple.ipynb` - Stack machine examples
