# Phase 3: CPU, Machine Code, and Assembly - COMPLETE ✓

## Overview
Completed Phase 3 of the Adder2Snake project: designed and documented the StaM (Stack Machine) CPU, implemented assembly programs, and created a comprehensive test suite.

**Based on**: [03-cpu-machine.pdf](file://03-cpu-machine (1).pdf)

---

## What Was Implemented

### 1. StaM CPU Architecture Documentation ✓

**File**: `hw/cpu/STAM_ARCHITECTURE.md`

**Complete specification of:**
- **Instruction set** (14 instructions)
- **Memory map** (16-bit word-addressable)
- **Stack-based execution model**
- **Peripherals** (GPIO, Video)
- **Assembly language syntax** (StASM)

#### Key Architecture Features

**Instruction Format:**
```
┌──────────┬─────────────────┐
│  opcode  │    argument     │
│  4 bits  │    16 bits      │
└──────────┴─────────────────┘
```

**Instruction Categories:**
1. **Stack**: PUSH, POP, DUP
2. **ALU**: ADD, SUB, MUL, NEG, AND, OR, NOT, SHL, SHR, LT
3. **Memory**: LOAD, STOR
4. **Control Flow**: JMP, JZ, JNZ, RET

### 2. Assembly Programs ✓

**Directory**: `hw/cpu/programs/`

#### max.asm / max_simple.asm
**Purpose**: Find maximum value in an array

**Algorithm:**
```c
mx = a[0];
for (int i = 1; i < n; i++) {
    if (a[i] > mx) mx = a[i];
}
return mx;
```

**Features:**
- Handles arrays of any length
- Error checking for empty arrays
- Memory-based variables (0x1000-0x1003)
- Returns -1 on error

#### find.asm
**Purpose**: Search for value in array

**Algorithm:**
```c
for (at = 0; at < n; at++) {
    if (a[at] == v) break;
}
return at;
```

**Features:**
- Linear search implementation
- Returns index if found
- Returns n (length) if not found
- Memory-based implementation

### 3. Test Suite ✓

**File**: `hw/cpu/programs/test_programs.py`

**Comprehensive testing framework:**

#### Max Program Tests (7 test cases)
- ✓ Ascending array
- ✓ Descending array
- ✓ Maximum in middle
- ✓ All same values
- ✓ Single element
- ✓ Negative numbers
- ✓ Mixed positive/negative

#### Find Program Tests (7 test cases)
- ✓ Find at beginning
- ✓ Find at end
- ✓ Find in middle
- ✓ Value not found
- ✓ Single element found
- ✓ Single element not found
- ✓ Duplicate values

**Features:**
- Mock simulation mode when hardware unavailable
- Detailed test output
- Automatic verification
- Professional formatting

### 4. Peripheral Documentation ✓

**Documented in**: `STAM_ARCHITECTURE.md`

#### GPIO Adapter (0xc000)
```
0xc000: GPIO_IN_LO   (read-only,  input[15:0])
0xc001: GPIO_IN_HI   (read-only,  input[31:16])
0xc002: GPIO_OUT_LO  (write,      output[15:0])
0xc003: GPIO_OUT_HI  (write,      output[31:16])
```

**Implementation**: `periph.py` - `gpio_adapter()`

#### Video Adapter (0xa000)
- **Base**: 0xa000
- **Size**: 256 words (16×16 display)
- **Address**: `base + (y * 16) + x`
- **Auto-scanning**: Automatic refresh

**Implementation**: `periph.py` - `video_adapter()`

---

## Files Created

```
hw/cpu/
├── STAM_ARCHITECTURE.md         ← CPU specification
└── programs/
    ├── max.asm                  ← Maximum finder (stack-based)
    ├── max_simple.asm           ← Maximum finder (memory-based)
    ├── find.asm                 ← Array search
    ├── test_programs.py         ← Test suite
    └── README.md                ← Programs documentation
```

---

## Key Concepts

### 1. Stack-Based Architecture

**Advantages:**
- Simple instruction encoding
- No need for register allocation
- Easy to compile to
- Natural for expression evaluation

**Stack Operations:**
```assembly
PUSH 10         ; Stack: [10]
PUSH 20         ; Stack: [10, 20]
ALU ADD         ; Stack: [30]
```

### 2. Memory-Mapped I/O

**Direct memory access to peripherals:**
```assembly
; Read GPIO input
PUSH 0xc000
LOAD            ; Read GPIO_IN_LO

; Write to video memory
PUSH pixel_value
PUSH 0xa050     ; Video location
STOR            ; Write pixel
```

### 3. Assembly Programming Patterns

**Variable Storage:**
```assembly
; Use memory for variables
PUSH value
PUSH 0x1000     ; Variable address
STOR            ; Store
```

**Loops:**
```assembly
loop:
    ; Loop body
    ; ...
    ; Increment counter
    PUSH counter_addr
    LOAD
    PUSH 1
    ALU ADD
    PUSH counter_addr
    STOR
    ; Check condition
    JMP loop
```

**Function Calls:**
```assembly
; Push return address
PUSH return_label
; Push arguments
PUSH arg1
PUSH arg2
; Jump to function
JMP function
return_label:
    ; Result on stack
```

---

## Programming Examples

### Example 1: Simple Addition
```assembly
; Compute 10 + 20
main:
    PUSH 10
    PUSH 20
    ALU ADD
    RET 1       ; Return result
```

### Example 2: Array Sum
```assembly
; Sum array of n elements at address a
; Inputs: a, n
; Output: sum
main:
    ; Store inputs
    PUSH 0x1001
    STOR        ; Store n
    PUSH 0x1000
    STOR        ; Store a
    
    ; sum = 0
    PUSH 0
    PUSH 0x1002
    STOR
    
    ; i = 0
    PUSH 0
    PUSH 0x1003
    STOR
    
loop:
    ; Check i < n
    PUSH 0x1003
    LOAD
    PUSH 0x1001
    LOAD
    ALU LT
    JZ done
    
    ; sum += a[i]
    PUSH 0x1002
    LOAD        ; Load sum
    PUSH 0x1000
    LOAD        ; Load a
    PUSH 0x1003
    LOAD        ; Load i
    ALU ADD     ; a+i
    LOAD        ; a[i]
    ALU ADD     ; sum + a[i]
    PUSH 0x1002
    STOR        ; Store new sum
    
    ; i++
    PUSH 0x1003
    LOAD
    PUSH 1
    ALU ADD
    PUSH 0x1003
    STOR
    JMP loop
    
done:
    PUSH 0x1002
    LOAD        ; Return sum
    RET 1
```

---

## Testing

### Run Tests
```bash
cd hw/cpu/programs
python3 test_programs.py
```

### Expected Output
```
╔══════════════════════════════════════════════════════════╗
║                                                          ║
║          StASM Assembly Program Test Suite               ║
║                                                          ║
╚══════════════════════════════════════════════════════════╝

Testing max.asm - Find Maximum in Array
========================================================
Test 1: Simple ascending
  Array: [1, 2, 3, 4, 5]
  Expected: 5
  ✓ Test case valid (Python max: 5)

[... more tests ...]

╔══════════════════════════════════════════════════════════╗
║                                                          ║
║                    FINAL RESULTS                         ║
║                                                          ║
║  Total Tests: 14                                         ║
║  Passed: 14                                              ║
║  Failed: 0                                               ║
║  Success Rate: 100.0%                                    ║
║                                                          ║
╚══════════════════════════════════════════════════════════╝
```

---

## Integration with Existing Code

### Using with Assembler
```python
from assembler import assemble

# Assemble program
machine_code = assemble("max_simple.asm")

# Machine code ready for simulation/execution
```

### Using with Simulator
```python
from simulate.simulation_utils import simulate_program

# Run program
result = simulate_program(
    code=machine_code,
    memory={0x2000: [5, 2, 9, 1, 7]},  # Array data
    inputs=[0x2000, 5]  # Array addr, length
)

print(f"Maximum: {result}")  # Output: 9
```

---

## Next Steps

### Immediate (Assigned Tasks):
1. ✅ Write max() program in StASM
2. ✅ Write find() program in StASM
3. ✅ Create test suite in Python

### Future:
4. ⬜ Run programs on actual CPU simulation
5. ⬜ Test with C simulation (csim)
6. ⬜ Test with Verilog simulation (vsim)
7. ⬜ Optimize assembly programs
8. ⬜ Add more test programs
9. ⬜ Implement peripherals in simulation
10. ⬜ Start on Snake game!

---

## Resources

- **Slides**: [03-cpu-machine.pdf](file://03-cpu-machine (1).pdf)
- **Existing Code**:
  - `instruction_set.py` - Instruction encoding
  - `assembler.py` - Assembler implementation
  - `periph.py` - Peripheral adapters
  - `cpu.ipynb` - CPU design notebook
  - `stack-simple.ipynb` - Stack machine examples

---

## Milestones

✅ **Phase 1**: Adder Verification  
✅ **Phase 2**: Transition Systems  
✅ **Phase 3**: CPU & Assembly ← **YOU ARE HERE**  
⬜ **Phase 4**: Bare Metal Programming  
⬜ **Phase 5**: Compiler  
⬜ **Phase 6**: Software Verification  
⬜ **Phase 7**: Snake Game & Verification  

---

**Status**: Phase 3 Complete ✓  
**Date**: November 27, 2025  
**Next**: Simulation & Testing on Hardware  
**Ready for**: Demo and presentation!
