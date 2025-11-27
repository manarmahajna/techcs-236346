# Getting Started with Adder2Snake Project

## Quick Overview

This is the **Adder2Snake** project - an educational journey from basic adders to a complete computer system with the Snake game, all formally verified!

Inspired by **Nand2Tetris**, this project teaches:
- Hardware design with PyRTL
- Formal verification with Z3
- Compiler construction
- Software/hardware co-design

## What's Been Completed: Warmup Exercise ✓

### Files Created

#### 1. Core Verification Infrastructure
- `hw/base/circuit.py` - **net_to_smt** function for PyRTL→Z3 translation

#### 2. Arithmetic Circuits
- `hw/arith/adder.py` - Parametric k-bit adder
- `hw/arith/verify_adder.py` - Verification script with benchmarking
- `hw/arith/verify_adder.ipynb` - Interactive verification notebook
- `hw/arith/README.md` - Documentation

#### 3. Compiler Backend
- `sw/compiler/backend.py` - Stack-based compiler backend

#### 4. CPU Design
- `hw/cpu/cpu.ipynb` - Stack-based CPU implementation

## Quick Start

### 1. View the Adder Verification Notebook
```bash
cd hw/arith
jupyter lab verify_adder.ipynb
```

### 2. Run Verification from Command Line
```bash
cd hw/arith
python3 verify_adder.py
```

### 3. Test Custom Bit Width
```python
from adder import make_adder
import pyrtl

# Create an 8-bit adder
a, b, sum_out = make_adder(8)

# Simulate
sim = pyrtl.Simulation()
sim.step({'a': 42, 'b': 27})
print(f"42 + 27 = {sim.inspect('sum')}")  # Output: 69
```

### 4. Explore the Base Verification Tutorial
```bash
cd hw/base
jupyter lab verify.ipynb
```

## Project Roadmap

According to the course slides:

- [x] **Phase 1: Adder verification** (COMPLETE)
- [x] **Phase 2: Transition systems** (COMPLETE) ← **YOU ARE HERE**
- [ ] Design a simple sequential processor
- [ ] Write bare metal programs (calculator, bootloader, memory allocator)
- [ ] Implement compiler back-end for ML-like language
- [ ] Verify formal properties of hardware and software
- [ ] Code the Snake game
- [ ] Verify Snake's correctness
- [ ] Extra creative features

## Key Technologies

- **PyRTL**: Python-based hardware description language
- **Z3**: SMT solver for formal verification
- **Jupyter**: Interactive development environment
- **Python 3**: Primary programming language

## Directory Structure

```
.
├── hw/                          # Hardware designs
│   ├── base/                   # Base verification infrastructure
│   │   ├── circuit.py         # ← net_to_smt (Phase 1)
│   │   ├── transition_system.py  # ← NEW: Phase 2
│   │   ├── verify_transition_systems.ipynb  # ← NEW: Phase 2
│   │   ├── verify_stack_machine.ipynb      # ← NEW: Phase 2
│   │   ├── verify.ipynb       # Tutorial notebook
│   │   ├── verification_utils.py
│   │   └── boilerplate.py
│   ├── arith/                  # Arithmetic circuits (Phase 1)
│   │   ├── adder.py
│   │   ├── verify_adder.py
│   │   ├── verify_adder.ipynb
│   │   └── README.md
│   └── cpu/                    # CPU design
│       ├── cpu.ipynb
│       ├── instruction_set.py
│       ├── assembler.py
│       └── simulate/
├── sw/                          # Software/compiler
│   ├── basics/
│   ├── compiler/
│   │   ├── backend.py         # Compiler backend
│   │   ├── parser.py
│   │   └── ir.py
│   └── verify/
└── src/                         # Web IDE
    ├── components/
    └── emulation/
```

## Resources

- **Course**: Technion 236346 - Hardware & Software Verification
- **Nand2Tetris**: https://www.coursera.org/learn/build-a-computer
- **PyRTL Docs**: https://pyrtl.readthedocs.io/
- **Z3Py Tutorial**: https://ericpony.github.io/z3py-tutorial/

## Next Steps

### Phase 2 Work (Current):
1. ✓ Review transition system verification in `hw/base/verify_transition_systems.ipynb`
2. ✓ Study stack machine verification in `hw/base/verify_stack_machine.ipynb`
3. ✓ Understand CHC encoding for hardware

### Phase 3 Preparation:
4. Study the CPU design in `hw/cpu/cpu.ipynb`
5. Understand the compiler backend in `sw/compiler/backend.py`
6. Design your sequential processor
7. Prepare for milestone presentations

## Documentation

### Phase 1 (Adders):
- `WARMUP_COMPLETE.md` - Phase 1 summary
- `hw/arith/README.md` - Arithmetic circuits

### Phase 2 (Transition Systems):
- `PHASE2_COMPLETE.md` - Phase 2 summary
- `hw/base/verify_transition_systems.ipynb` - Transition systems tutorial
- `hw/base/verify_stack_machine.ipynb` - Stack verification

### General:
- `hw/base/verify.ipynb` - Base verification tutorial

---

**Good luck with your Adder2Snake journey!** 🐍

From basic adders to a verified computer system - you're on your way!
