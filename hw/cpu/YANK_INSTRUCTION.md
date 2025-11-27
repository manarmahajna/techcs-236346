# YANK Instruction Specification

**Added in**: Phase 4 (Software Stack)  
**Purpose**: Stack manipulation for function calling convention

## Instruction Format

```
YANK (i, j)
```

**Encoding**: `i | (j << 4)` - packed into 16-bit argument field

## Semantics

**Operation**: Delete `j` consecutive stack elements starting from index `i` and going down.

**Before**:
```
Stack: [..., r_{i+j}, ..., r_{i+1}, r_i, r_{i-1}, ..., r_1, r_0]
                       └───────┬───────┘
                          j elements
```

**After**:
```
Stack: [..., r_{i+j}, r_{i-1}, ..., r_1, r_0]
```

## Use Case: Function Returns

When a function returns, we need to clean up:
- Arguments that were passed (k arguments)
- Local variables (m variables)  
- Return address

**Return sequence**:
```assembly
YANK 1, k+m+1    ; Remove args, locals, ret addr (keeping return value at top)
POP 2            ; (implementation detail)
RET 1            ; Return with value
```

## Examples

### Example 1: Remove Single Element
```
Before: [10, 20, 30, 40, 50]  (r_4, r_3, r_2, r_1, r_0)
YANK 2, 1
After:  [10, 20, 40, 50]      (r_3, r_2, r_1, r_0)
```
Removed element at index 2 (value 30).

### Example 2: Remove Multiple Elements
```
Before: [10, 20, 30, 40, 50, 60]  (indices 5,4,3,2,1,0)
YANK 3, 2
After:  [10, 20, 50, 60]          (indices 3,2,1,0)
```
Removed 2 elements starting at index 3 (values 30, 40).

### Example 3: Function Return Cleanup
```
; Function called with 2 args, has 1 local, returns value
; Stack before return: [ret_addr, arg1, arg2, local, result]
;                      [r_4,      r_3,  r_2,  r_1,   r_0]

YANK 1, 4        ; Keep result (r_0), remove local, arg2, arg1, ret_addr
; Stack now: [result]
RET 1            ; Return result to caller
```

## Implementation Notes

### Stack Manipulation Algorithm

```python
def yank(stack, i, j):
    """
    Remove j elements starting at index i from stack.
    Stack is indexed from top: r_0, r_1, r_2, ...
    """
    # Remove elements from [i] to [i+j-1]
    for k in range(j):
        stack.pop(i)
    return stack
```

### Hardware Implementation

In PyRTL/circuit:
1. Read stack pointer (sp)
2. Calculate new sp: `sp' = sp - j`
3. Copy elements:
   - For k from 0 to (i-1): `stack[k]' = stack[k]`
   - For k from i onward: `stack[k]' = stack[k+j]`
4. Update stack pointer

### Encoding Details

**Argument field (16 bits)**:
```
┌────────────┬────────────┐
│ j (high 12)│ i (low 4)  │
└────────────┴────────────┘
```

**Limits**:
- `i`: 0-15 (4 bits)
- `j`: 0-4095 (12 bits) - though practical limit is stack size

## ABI Calling Convention

### Function Call
```assembly
PUSH ret_label   ; Return address
PUSH arg_0       ; First argument
PUSH arg_1       ; Second argument
...
PUSH arg_k       ; Last argument
JMP function     ; Jump to function
ret_label:       ; Execution continues here after return
```

### Function Return
```assembly
; Inside function, after computing result
; Stack: [ret_addr, arg_0, ..., arg_k, local_0, ..., local_m, result]
; Want:  Jump to ret_addr with result on stack

YANK 1, k+m+1    ; Remove everything except result
                 ; Stack now: [ret_addr, result]
POP 2            ; Pop 2? (need to check actual semantics)
RET 1            ; Indirect jump to ret_addr, push result
```

## Verification

### Specification

**Pre**: `stack_depth > i + j`

**Post**: 
```
∀k < i:      stack'[k] = stack[k]
∀k ≥ i:      stack'[k] = stack[k + j]
sp' = sp - j
```

### CHC Encoding

```python
import z3

# State variables
sp = z3.BitVec('sp', 16)
sp_next = z3.BitVec("sp'", 16)
stack = z3.Array('stack', z3.BitVecSort(16), z3.BitVecSort(16))
stack_next = z3.Array("stack'", z3.BitVecSort(16), z3.BitVecSort(16))

# Parameters
i = z3.BitVec('i', 4)
j = z3.BitVec('j', 12)

# Precondition
pre = z3.UGE(sp, i + j)

# Postcondition
post = z3.And(
    sp_next == sp - j,
    # Elements below i unchanged
    z3.ForAll([k], z3.Implies(z3.ULT(k, i),
                               z3.Select(stack_next, k) == z3.Select(stack, k))),
    # Elements from i upward shifted down by j
    z3.ForAll([k], z3.Implies(z3.UGE(k, i),
                               z3.Select(stack_next, k) == z3.Select(stack, k + j)))
)

# Correctness: pre => post
verify = z3.Implies(pre, post)
```

## See Also

- `instruction_set.py` - Add YANK opcode
- `backend.py` - Use YANK for function returns
- Phase 4 documentation for calling convention
