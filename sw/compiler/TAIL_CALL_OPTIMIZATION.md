# Tail Call Optimization

**Purpose**: Prevent stack overflow in recursive functions by reusing the caller's stack frame.

## Problem: Regular Recursion

Without tail call optimization:
```
factorial(n):
  if n == 0: return 1
  else: return n * factorial(n-1)
```

**Stack growth**:
```
factorial(5)
  → factorial(4)
    → factorial(3)
      → factorial(2)
        → factorial(1)
          → factorial(0) = 1
        ← 1
      ← 2
    ← 6
  ← 24
← 120
```

Each call creates a new stack frame → **Stack overflow for large n!**

## Solution: Tail Recursion

Rewrite using accumulator:
```
factorial(n) = fact_aux(n, 1)

fact_aux(n, acc):
  if n == 0: return acc
  else: return fact_aux(n-1, n*acc)  ← Tail call!
```

**Key property**: The recursive call is the **last operation** (in tail position).

## Tail Call Optimization

Instead of creating new stack frame, **reuse the current one**:

### Regular Call
```assembly
; Call function
PUSH ret_addr
PUSH arg1
PUSH arg2
JMP function
ret_addr:
; Continue after return
```

Stack: `[..., ret_addr, arg1, arg2]`

### Tail Call
```assembly
; Tail call: No need to save return address!
; Reuse caller's return address
YANK k, nargs     ; Remove old arguments
PUSH new_arg1
PUSH new_arg2
JMP function      ; Return directly to caller's caller
```

Stack: `[..., ret_addr, new_arg1, new_arg2]`

## Implementation in StaML

### Tail Call Indicator: `.`

```staml
fact(1) = fact_aux $0 1

fact_aux(2) =
  if 0 < $1
    then .fact_aux ($1 - 1) ($0 * $1)  ← . indicates tail call
    else $0
```

The `.` prefix tells the compiler to generate tail call code.

## Compiler Code Generation

### Regular Call
```python
def emit_call(func, args):
    self.emit(('PUSH', ret_label))
    for arg in args:
        self.emit_expr(arg)
    self.emit(('JMP', func))
    self.emit(ret_label)
```

### Tail Call
```python
def emit_tail_call(func, args):
    # Remove old arguments using YANK
    # YANK can handle up to 15 positions
    if nargs <= 15:
        self.emit(('YANK', (len(args), self.sig.nargs)))
    
    # Push new arguments
    for arg in args:
        self.emit_expr(arg)
    
    # Jump directly (reuse caller's return address)
    self.emit(('JMP', func))
```

## Examples

### Example 1: Factorial
```staml
/* Tail-recursive factorial */
fact(1) = fact_aux $0 1

fact_aux(2) =
    if $1 < 1
    then $0                           // Base case: return accumulator
    else .fact_aux ($0 * $1) ($1 - 1) // Tail call with updated accumulator
```

**Assembly**:
```assembly
fact_aux:
    ; Check if $1 < 1
    DUP 0           ; Get $1 (n)
    PUSH 1
    ALU LT
    JZ recurse
    
    ; Base case: return $0 (accumulator)
    DUP 1           ; Get $0
    RET 1
    
recurse:
    ; Tail call: fact_aux($0 * $1, $1 - 1)
    ; Stack: [ret_addr, acc, n]
    
    ; Compute new args
    DUP 1           ; acc
    DUP 1           ; n
    ALU MUL         ; acc * n (new acc)
    
    DUP 1           ; n
    PUSH 1
    ALU SUB         ; n - 1 (new n)
    
    ; Replace old args with new args
    YANK 2, 2       ; Remove old acc and n, keep new args
    
    JMP fact_aux    ; Tail call!
```

### Example 2: List Sum
```staml
/* Sum elements of array */
sum_array(2) = sum_aux $0 $1 0

sum_aux(3) =
    if $1 < 1
    then $2                                    // Return accumulator
    else .sum_aux $0 ($1 - 1) ($2 + mem_peek($0 + $1 - 1))
```

### Example 3: Wait Loop (Keyboard)
```staml
wait_aux(1) =
    if (mem_peek 0xc001) - $0
    then mem_peek 0xc000        // Key pressed: return
    else .wait_aux $0           // Tail recursive poll
```

**This is critical!** Without tail call optimization, keyboard polling would overflow the stack.

## Limitations

### YANK Constraint
With current architecture, YANK can move at most 15 positions:
- `i`: 4 bits (0-15)
- `j`: 12 bits (0-4095)

**Practical limit**: Functions with ≤ 4 arguments for tail calls.

### Mutual Recursion
Tail call optimization works for:
- Direct recursion: `f` calls `f`
- Mutual recursion: `f` calls `g` calls `f` (both must be tail calls)

### Non-Tail Recursion
If operation follows the recursive call, **not a tail call**:
```staml
bad_fact(1) =
    if $0 < 1
    then 1
    else $0 * bad_fact($0 - 1)  // NOT tail call! (* comes after)
```

## Verification

### Property to Verify
For tail-recursive function:
- **Invariant**: Stack depth remains constant
- **Termination**: Each call brings closer to base case
- **Correctness**: Final result matches specification

### Example: Factorial Verification
```
Spec: fact(n) = n!

Invariant: fact_aux(acc, n) will return acc * n!

Proof by induction:
  Base: n = 0 → return acc = acc * 0! ✓
  Step: Assume holds for n
        fact_aux(acc, n+1)
        = fact_aux(acc*(n+1), n)      [tail call]
        = acc*(n+1) * n!               [by IH]
        = acc * (n+1)!                 ✓
```

## Benefits

1. **No Stack Overflow**: Constant stack space
2. **Performance**: Faster (no frame allocation)
3. **Enables Loops**: Tail recursion = loop
4. **Required for**:
   - Event loops
   - Keyboard/GPIO polling
   - Game main loops
   - Server request handlers

## See Also

- `sw/compiler/backend.py` - Tail call code generation
- `sw/verify/keyboard_controller.staml` - Tail call example
- Phase 5 documentation for more examples
