# Adder2Snake: Hardware and Software Verification Project

**Course**: 236346 - Technion  
**Project**: Building a Verified Computer System from Adders to Snake Game

---

## 🎯 **Project Overview**

This project takes you on a journey from basic adders to a complete, formally verified computer system running the Snake game. Inspired by Nand2Tetris, we emphasize formal verification at every step.

### What Makes This Special?
- **Formal Verification**: Every component proven correct using Z3 SMT solver
- **Complete System**: From hardware gates to running software
- **Educational**: Learn hardware design, verification, and systems programming
- **Open Source**: All code available for learning and extension

---

## 📊 **Current Progress: 7/7 Phases Complete** ✅

| Phase | Status | Description |
|-------|--------|-------------|
| 1. Adders | ✅ **Complete** | Parametric adder + verification |
| 2. Transition Systems | ✅ **Complete** | State verification + CHCs |
| 3. CPU & Assembly | ✅ **Complete** | Stack machine + programs |
| 4. Software Stack | ✅ **Complete** | Bootloader + stdlib + ISA verification |
| 5. Loop Verification | ✅ **Complete** | Tail calls + program verification + keyboard |
| 6. Advanced Verification | ✅ **Complete**  | Complex program properties |
| 7. Snake Game | ✅ **Complete**  | Complete system + verification |

---

## 🚀 **Quick Start**

### Option 1: Interactive Exploration
```bash
# Phase 1: Adder Verification
cd hw/arith
jupyter lab verify_adder.ipynb

# Phase 2: Transition Systems
cd hw/base
jupyter lab verify_transition_systems.ipynb

# Phase 3: Assembly Programming
cd hw/cpu/programs
python3 test_programs.py
```

### Option 2: Command Line
```bash
# Verify k-bit adder
cd hw/arith && python3 verify_adder.py

# Test assembly programs
cd hw/cpu/programs && python3 test_programs.py
```

---

## 📚 **Documentation**

### Getting Started
- **[GETTING_STARTED.md](GETTING_STARTED.md)** - Quick start guide
- **[PROJECT_STATUS.md](PROJECT_STATUS.md)** - Detailed status

### Phase Documentation
- **[WARMUP_COMPLETE.md](WARMUP_COMPLETE.md)** - Phase 1: Adders
- **[PHASE2_COMPLETE.md](PHASE2_COMPLETE.md)** - Phase 2: State
- **[PHASE3_COMPLETE.md](PHASE3_COMPLETE.md)** - Phase 3: CPU
- **[PHASE4_COMPLETE.md](PHASE4_COMPLETE.md)** - Phase 4: Software Stack
- **[PHASE5_COMPLETE.md](PHASE5_COMPLETE.md)** - Phase 5: Loop Verification

### Technical Specs
- **[hw/arith/README.md](hw/arith/README.md)** - Arithmetic circuits
- **[hw/cpu/STAM_ARCHITECTURE.md](hw/cpu/STAM_ARCHITECTURE.md)** - CPU specification
- **[hw/cpu/programs/README.md](hw/cpu/programs/README.md)** - Assembly programs

---

## 🏗️ **Architecture**

### StaM CPU (Stack Machine)
- **16-bit** word-addressable architecture
- **14 instructions**: Stack, ALU, Memory, Control
- **Memory-mapped I/O**: GPIO, Video display
- **Stack-based**: Simple, verifiable execution model

### Instruction Set
```
Stack:    PUSH, POP, DUP
ALU:      ADD, SUB, MUL, NEG, AND, OR, NOT, SHL, SHR, LT
Memory:   LOAD, STOR
Control:  JMP, JZ, JNZ, RET
```

---

## 🧪 **What's Verified**

### Hardware (Phase 1-2)
- ✅ **Adders**: k-bit parametric adder (1-32 bits)
- ✅ **Counter**: 2-bit counter with wrap-around
- ✅ **Memory Loop**: Increment with invariant preservation
- ✅ **Stack Operations**: PUSH/POP specifications

### Software (Phase 3)
- ✅ **max.asm**: Find maximum in array (7 tests)
- ✅ **find.asm**: Search for value (7 tests)
- ✅ **Test Coverage**: 14/14 tests passing

---

## 💻 **Code Examples**

### Assembly Program (StASM)
```assembly
; Find maximum in array
main:
    PUSH 0x2000     ; Array address
    LOAD            ; Load first element
    PUSH 1          ; Start at index 1
    
loop:
    ; Compare and update max
    ; ... loop body ...
    JMP loop
    
done:
    RET 1           ; Return maximum
```

### Verification (Python + Z3)
```python
from circuit import net_to_smt
import pyrtl, z3

# Create circuit
a, b, sum_out = make_adder(8)

# Translate to SMT
wires, ops, assertions = net_to_smt(pyrtl.working_block())

# Verify correctness
solver = z3.Solver()
for assertion in assertions:
    solver.add(assertion)

# Prove: sum = (a + b) mod 2^8
correctness = (wires['sum'] == (wires['a'] + wires['b'])[:8])
solver.add(z3.Not(correctness))

assert solver.check() == z3.unsat  # No counterexample!
```

---

## 🔧 **Technologies**

| Technology | Purpose |
|-----------|---------|
| **PyRTL** | Hardware description language |
| **Z3** | SMT solver for verification |
| **Python** | Implementation & scripting |
| **Jupyter** | Interactive development |
| **C++** | High-performance simulation |
| **Node.js** | Web-based IDE |

---

## 📁 **Project Structure**

```
project/
├── hw/
│   ├── base/              # Verification infrastructure
│   │   ├── circuit.py     # PyRTL→Z3 translation
│   │   ├── transition_system.py  # State verification
│   │   └── *.ipynb        # Tutorials
│   ├── arith/             # Arithmetic circuits
│   │   └── verify_adder.* # Adder verification
│   └── cpu/               # CPU design
│       ├── STAM_ARCHITECTURE.md  # Specification
│       ├── programs/      # Assembly programs
│       ├── assembler.py   # Assembler
│       └── simulate/      # Simulation
└── sw/
    ├── basics/            # Basic programs
    ├── compiler/          # Compiler backend
    │   └── backend.py     # Stack code generation
    └── verify/            # Software verification
```

---




---

## 🌟 **Highlights**

### Phase 1: Adder Verification
- Parametric k-bit adder verified for k=1 to k=32
- Performance plots showing verification time vs. bit width
- Complete automation of equivalence checking

### Phase 2: Transition Systems
- State verification using init/step relations
- CHC-based automatic invariant inference
- PUSH/POP formal specifications

### Phase 3: CPU & Assembly
- Complete ISA with 14 instructions
- Two working assembly programs (max, find)
- Comprehensive test suite with 100% pass rate

### Phase 4: Software Stack
- YANK instruction for efficient stack manipulation
- Bootloader with formal verification (GPIO → RAM)
- Standard library with 20+ functions
- Complete instruction set formal specifications
- ABI calling convention

---


---

## 📖 **Resources**

### Course Materials
- [01-Adder-2-Snake.pdf](file://01-Adder-2-Snake.pdf) - Project intro
- [02-transition-system.pdf](file://02-transition-system.pdf) - State verification
- [03-cpu-machine.pdf](file://03-cpu-machine (1).pdf) - CPU design

### External Links
- **Nand2Tetris**: https://www.coursera.org/learn/build-a-computer
- **PyRTL Documentation**: https://pyrtl.readthedocs.io/
- **Z3 Guide**: https://microsoft.github.io/z3guide/
- **CHCs in Z3**: https://microsoft.github.io/z3guide/programming/Fixedpoints

---

lana abu romi - 322836271
manar mahagna - 211437397
