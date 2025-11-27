# Phase 2: Transition Systems - COMPLETE ✓

## Overview
Completed the second phase of the Adder2Snake project focusing on stateful hardware verification using transition systems and Constrained Horn Clauses (CHCs).

Based on: **[02-transition-system.pdf](file://02-transition-system.pdf)**

## What Was Implemented

### 1. Transition System Framework (`hw/base/transition_system.py`) ✓

**New module** for encoding and verifying stateful hardware:

**Key Features:**
- `TransitionSystem` class for modeling init/step relations
- `net_to_smt_stateful()` - Enhanced translation handling state
- `verify_invariant()` - Checks initiation and consecution
- Full support for registers and memory arrays

**State Handling:**
- Registers: Current state (`r`) and next state (`r'`)
- Memory: Current (`mem`) and next (`mem'`) arrays
- Automatic Z3 variable creation with proper naming

### 2. Transition System Verification Notebook ✓

**File**: `hw/base/verify_transition_systems.ipynb`

**Examples:**
1. **Simple Counter**
   - Init: `r = 0`
   - Step: `r' = r + 1 (mod 4)`
   - Verifies wrap-around behavior

2. **Memory Loop**
   - Increments `mem[sp]` each cycle
   - Sets `mem[0] = 0` always
   - Proves invariant: `mem[0]` is always 0

3. **CHC Encoding**
   - Demonstrates Constrained Horn Clauses
   - Uses Z3's Spacer engine for automatic verification
   - Shows how to encode init => Inv => Safety

### 3. Stack Machine Verification ✓

**File**: `hw/base/verify_stack_machine.ipynb`

**Complete Implementation:**

#### Stack Machine Model
```
State: sp (stack pointer), mem (stack memory)
Operations:
  PUSH(val): mem[sp] := val; sp := sp + 1
  POP():     sp := sp - 1; return mem[sp]
```

#### Formal Specifications

**PUSH Specification:**
- **Pre**: `sp < 8` (not full)
- **Post**: `sp' = sp + 1`, `mem'[sp] = val`, others unchanged

**POP Specification:**
- **Pre**: `sp > 0` (not empty)
- **Post**: `sp' = sp - 1`, `pop_val = mem[sp-1]`, mem unchanged

#### Verification Results
- ✓ PUSH spec verified correct
- ✓ POP spec verified correct
- ✓ Test program (PUSH-PUSH-POP) simulated successfully
- ✓ CHC encoding proves `sp` stays within bounds

## Files Created

```
hw/base/
├── circuit.py                        ← Phase 1 (enhanced)
├── transition_system.py              ← NEW: Transition systems & CHCs
├── verify_transition_systems.ipynb   ← NEW: Counter & memory examples
└── verify_stack_machine.ipynb        ← NEW: Stack PUSH/POP verification
```

## Key Concepts Demonstrated

### 1. Transition Systems
- **Init formula**: Describes initial state
- **Step formula**: Relates current state to next state
- **Invariant**: Property preserved by transitions

### 2. Verification Pattern
```
Initiation:   init(s) => Inv(s)
Consecution:  Inv(s) ∧ step(s,s') => Inv(s')
Safety:       Inv(s) => Property(s)
```

### 3. CHCs (Constrained Horn Clauses)
```
init(state) => Inv(state)
Inv(state) ∧ transition => Inv(state')
Inv(state) => SafetyProperty
```

Z3's Spacer engine automatically infers invariants!

### 4. Memory Modeling
- Z3 Arrays: `Array(KeySort, ValueSort)`
- Read: `Select(array, index)`
- Write: `Store(array, index, value)`
- Frame conditions: Other locations unchanged

## Example Usage

### Verify a Counter
```python
from transition_system import net_to_smt_stateful
import z3

# Create state variables
r_curr = z3.BitVec('r', 2)
r_next = z3.BitVec("r'", 2)

# Define transition
init = (r_curr == 0)
step = (r_next == (r_curr + 1) % 4)
inv = z3.BoolVal(True)  # Always holds

# Verify
verify_invariant(init, step, inv, ['r'])
```

### Verify Stack Operations
```python
# See verify_stack_machine.ipynb for complete examples
# - PUSH/POP specifications
# - Test program simulation
# - CHC encoding
```

## Warmup Exercise Status

From **02-transition-system.pdf**:

1. ✅ Extend `net_to_smt` to encode state (memory and registers)
2. ✅ Test it by verifying memory loop automatically
3. ✅ Encode stack machine as CHCs using `net_to_smt`
4. ✅ Create test case with PUSH/POP sequence
5. ✅ Specify PUSH/POP semantics (pre/post conditions)
6. ✅ Verify circuit conforms to specifications

**All tasks complete!**

## Next Steps

According to the slides:

### Next Session (2 weeks):
- Define our processor and machine language
- Simulate & test designs
- Live hacking session with tips and guidance

### Required Software:
- ✓ Python 3.x + Jupyter Lab
- ✓ C++ Compiler (for simulation)
- ✓ GNU Make
- ✓ Node.js and NPM (for web IDE)

### Future Milestones:
1. ✅ Adder verification (Phase 1)
2. ✅ Transition systems (Phase 2) ← **YOU ARE HERE**
3. ⬜ Processor design
4. ⬜ Bare metal programs
5. ⬜ Compiler implementation
6. ⬜ Snake game
7. ⬜ Snake verification

## Resources

- **Course Slides**: [02-transition-system.pdf](file://02-transition-system.pdf)
- **PyRTL Simulation**: https://pyrtl.readthedocs.io/en/latest/simulations.html
- **Z3 Arrays**: https://z3prover.github.io/api/html/namespacez3py.html#arrays
- **CHCs in Z3**: https://microsoft.github.io/z3guide/programming/Fixedpoints

## Key Achievements

1. **Complete transition system framework** for stateful verification
2. **Working CHC encoding** that Z3 can solve automatically
3. **Formal specifications** for stack operations
4. **End-to-end verification** from circuit to proof

This provides the foundation for verifying the full CPU and stack machine in the next phases!

---
**Status**: Phase 2 Complete ✓  
**Date**: November 27, 2025  
**Next Milestone**: Processor Definition & Machine Language
