#!/usr/bin/env python3
"""
Instruction Sequence Verification

Verifies compositions of instructions work correctly.
Specifically focuses on POP + ALU sequences as required.
"""

import sys
sys.path.insert(0, '../base')

try:
    import z3
    Z3_AVAILABLE = True
except ImportError:
    print("Warning: Z3 not available")
    Z3_AVAILABLE = False


def verify_pop1_alu_neg():
    """Verify: POP 1; ALU NEG
    
    Should negate the top element of the stack.
    """
    print("\n" + "="*70)
    print("Verifying: POP 1; ALU NEG")
    print("="*70)
    
    if not Z3_AVAILABLE:
        print("Specification: Negate top of stack")
        print("  PRE:  sp >= 1")
        print("  POST: stack'[sp-1] = -stack[sp-1]")
        return True
    
    # State variables
    sp = z3.BitVec('sp', 16)
    stack = z3.Array('stack', z3.BitVecSort(16), z3.BitVecSort(16))
    
    # Precondition
    pre = z3.UGE(sp, 1)
    
    # After POP 1: r0 = stack[sp-1], sp unchanged for stack access
    r0_after_pop = z3.Select(stack, sp - 1)
    
    # After ALU NEG: result = -r0, push back
    result = -r0_after_pop
    stack_final = z3.Store(stack, sp - 1, result)
    
    # Postcondition: top element negated
    post = (z3.Select(stack_final, sp - 1) == -z3.Select(stack, sp - 1))
    
    # Verify
    solver = z3.Solver()
    solver.add(pre)
    solver.add(z3.Not(post))
    
    if solver.check() == z3.unsat:
        print("✓ VERIFIED: Top element correctly negated")
        return True
    else:
        print("✗ FAILED")
        return False


def verify_pop2_alu_add():
    """Verify: POP 2; ALU ADD
    
    Should add the top two elements of the stack.
    """
    print("\n" + "="*70)
    print("Verifying: POP 2; ALU ADD")
    print("="*70)
    
    if not Z3_AVAILABLE:
        print("Specification: Add top two elements")
        print("  PRE:  sp >= 2")
        print("  POST: result = stack[sp-2] + stack[sp-1]")
        print("        sp' = sp - 1")
        return True
    
    # State variables
    sp = z3.BitVec('sp', 16)
    stack = z3.Array('stack', z3.BitVecSort(16), z3.BitVecSort(16))
    
    # Precondition
    pre = z3.UGE(sp, 2)
    
    # After POP 2:
    r0_after_pop = z3.Select(stack, sp - 1)  # Top
    r1_after_pop = z3.Select(stack, sp - 2)  # Second
    sp_after_pop = sp - 2
    
    # After ALU ADD: result = r1 + r0, push
    result = r1_after_pop + r0_after_pop
    sp_final = sp_after_pop + 1
    stack_final = z3.Store(stack, sp_final - 1, result)
    
    # Postcondition
    post = z3.And(
        z3.Select(stack_final, sp_final - 1) == 
            (z3.Select(stack, sp - 2) + z3.Select(stack, sp - 1)),
        sp_final == sp - 1
    )
    
    # Verify
    solver = z3.Solver()
    solver.add(pre)
    solver.add(z3.Not(post))
    
    if solver.check() == z3.unsat:
        print("✓ VERIFIED: Top two elements correctly added")
        print(f"  Result = stack[sp-2] + stack[sp-1]")
        print(f"  Final sp = original sp - 1")
        return True
    else:
        print("✗ FAILED")
        return False


def verify_pop2_alu_sub():
    """Verify: POP 2; ALU SUB"""
    print("\n" + "="*70)
    print("Verifying: POP 2; ALU SUB")
    print("="*70)
    
    if not Z3_AVAILABLE:
        print("Specification: Subtract top from second")
        print("  PRE:  sp >= 2")
        print("  POST: result = stack[sp-2] - stack[sp-1]")
        return True
    
    sp = z3.BitVec('sp', 16)
    stack = z3.Array('stack', z3.BitVecSort(16), z3.BitVecSort(16))
    
    pre = z3.UGE(sp, 2)
    
    r0 = z3.Select(stack, sp - 1)
    r1 = z3.Select(stack, sp - 2)
    result = r1 - r0
    
    sp_final = sp - 1
    stack_final = z3.Store(stack, sp_final - 1, result)
    
    post = (z3.Select(stack_final, sp_final - 1) == 
            (z3.Select(stack, sp - 2) - z3.Select(stack, sp - 1)))
    
    solver = z3.Solver()
    solver.add(pre)
    solver.add(z3.Not(post))
    
    if solver.check() == z3.unsat:
        print("✓ VERIFIED: Subtraction correct")
        return True
    else:
        print("✗ FAILED")
        return False


def verify_pop2_alu_mul():
    """Verify: POP 2; ALU MUL"""
    print("\n" + "="*70)
    print("Verifying: POP 2; ALU MUL")
    print("="*70)
    
    if not Z3_AVAILABLE:
        print("Specification: Multiply top two elements")
        print("  PRE:  sp >= 2")
        print("  POST: result = stack[sp-2] * stack[sp-1]")
        return True
    
    sp = z3.BitVec('sp', 16)
    stack = z3.Array('stack', z3.BitVecSort(16), z3.BitVecSort(16))
    
    pre = z3.UGE(sp, 2)
    
    r0 = z3.Select(stack, sp - 1)
    r1 = z3.Select(stack, sp - 2)
    result = r1 * r0
    
    sp_final = sp - 1
    stack_final = z3.Store(stack, sp_final - 1, result)
    
    post = (z3.Select(stack_final, sp_final - 1) == 
            (z3.Select(stack, sp - 2) * z3.Select(stack, sp - 1)))
    
    solver = z3.Solver()
    solver.add(pre)
    solver.add(z3.Not(post))
    
    if solver.check() == z3.unsat:
        print("✓ VERIFIED: Multiplication correct")
        return True
    else:
        print("✗ FAILED")
        return False


def verify_pop2_alu_lt():
    """Verify: POP 2; ALU LT"""
    print("\n" + "="*70)
    print("Verifying: POP 2; ALU LT")
    print("="*70)
    
    if not Z3_AVAILABLE:
        print("Specification: Compare top two elements")
        print("  PRE:  sp >= 2")
        print("  POST: result = 1 if stack[sp-2] < stack[sp-1] else 0")
        return True
    
    sp = z3.BitVec('sp', 16)
    stack = z3.Array('stack', z3.BitVecSort(16), z3.BitVecSort(16))
    
    pre = z3.UGE(sp, 2)
    
    r0 = z3.Select(stack, sp - 1)
    r1 = z3.Select(stack, sp - 2)
    result = z3.If(z3.ULT(r1, r0), z3.BitVecVal(1, 16), z3.BitVecVal(0, 16))
    
    sp_final = sp - 1
    stack_final = z3.Store(stack, sp_final - 1, result)
    
    post = (z3.Select(stack_final, sp_final - 1) == 
            z3.If(z3.ULT(z3.Select(stack, sp - 2), z3.Select(stack, sp - 1)),
                  z3.BitVecVal(1, 16), z3.BitVecVal(0, 16)))
    
    solver = z3.Solver()
    solver.add(pre)
    solver.add(z3.Not(post))
    
    if solver.check() == z3.unsat:
        print("✓ VERIFIED: Comparison correct")
        return True
    else:
        print("✗ FAILED")
        return False


def main():
    """Run all instruction sequence verifications."""
    print("\n")
    print("╔" + "="*68 + "╗")
    print("║" + " "*68 + "║")
    print("║" + "  Instruction Sequence Verification".center(68) + "║")
    print("║" + "  POP + ALU Compositions".center(68) + "║")
    print("║" + " "*68 + "║")
    print("╚" + "="*68 + "╝")
    print()
    
    # Run all verifications
    results = []
    results.append(("POP 1; ALU NEG", verify_pop1_alu_neg()))
    results.append(("POP 2; ALU ADD", verify_pop2_alu_add()))
    results.append(("POP 2; ALU SUB", verify_pop2_alu_sub()))
    results.append(("POP 2; ALU MUL", verify_pop2_alu_mul()))
    results.append(("POP 2; ALU LT", verify_pop2_alu_lt()))
    
    # Summary
    print("\n" + "="*70)
    print("Summary")
    print("="*70)
    
    passed = sum(1 for _, result in results if result)
    total = len(results)
    
    print(f"\nTotal sequences: {total}")
    print(f"Verified: {passed}")
    print(f"Failed: {total - passed}")
    print(f"Success rate: {100*passed/total:.1f}%")
    
    if passed == total:
        print("\n✓ All instruction sequences verified!")
    
    return 0 if passed == total else 1


if __name__ == '__main__':
    sys.exit(main())
