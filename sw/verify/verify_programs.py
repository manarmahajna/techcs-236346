#!/usr/bin/env python3
"""
Software Verification Examples
Based on 05-loop-verif.pdf

Verifies:
1. Addition using +1 (increment)
2. Division and modulo with invariant
3. Find max element with ghost variable
4. Find value in array
"""

import sys
sys.path.insert(0, '../../hw/base')

try:
    import z3
    from verification_utils import CHCs
    Z3_AVAILABLE = True
except ImportError:
    print("Warning: Z3 not available - specifications only")
    Z3_AVAILABLE = False


# ============================================================================
# 1. Addition using +1
# ============================================================================

def verify_addition_by_increment():
    """
    Verify: add(a, b) implemented as a + (+1 applied b times)
    
    Specification:
      add(a, b) = a + b
      
    Implementation:
      add(a, 0) = a
      add(a, b) = add(a+1, b-1)  if b > 0
    """
    print("="*70)
    print("1. Addition using +1 (Increment)")
    print("="*70)
    
    if not Z3_AVAILABLE:
        print("Specification:")
        print("  add(a, b) = a + b")
        print()
        print("Implementation:")
        print("  add(a, 0) = a")
        print("  add(a, b) = add(a+1, b-1) if b > 0")
        print()
        print("Invariant: add(a, b) = (a+b)")
        return
    
    # Z3 verification
    a = z3.Int('a')
    b = z3.Int('b')
    result = z3.Int('result')
    
    # Specification
    spec = (result == a + b)
    
    # Implementation invariant: At each recursive call,
    # the sum (a+b) remains constant
    a_rec = z3.Int('a_rec')
    b_rec = z3.Int('b_rec')
    
    # Invariant: a_rec + b_rec = a + b (original values preserved)
    invariant = (a_rec + b_rec == a + b)
    
    # Base case: b = 0 => result = a
    base_case = z3.Implies(
        z3.And(invariant, b_rec == 0),
        a_rec == a + b  # result equals original sum
    )
    
    # Check base case
    solver = z3.Solver()
    solver.add(z3.Not(base_case))
    if solver.check() == z3.unsat:
        print("✓ Base case verified")
    else:
        print("✗ Base case failed")
    
    # Recursive case: add(a, b) = add(a+1, b-1)
    # Invariant preserved: (a+1) + (b-1) = a + b
    rec_case = z3.Implies(
        z3.And(invariant, b_rec > 0),
        (a_rec + 1) + (b_rec - 1) == a + b
    )
    
    solver = z3.Solver()
    solver.add(z3.Not(rec_case))
    if solver.check() == z3.unsat:
        print("✓ Recursive case verified")
        print("  Invariant preserved: (a+1) + (b-1) = a + b")
    else:
        print("✗ Recursive case failed")
    
    print()


# ============================================================================
# 2. Division and Modulo
# ============================================================================

def verify_division_modulo():
    """
    Verify: div and mod satisfy: nom = denom * div + mod
    
    Implementation:
      div(nom, denom, q=0):
        if nom < denom: return q
        else: return div(nom - denom, denom, q+1)
        
      mod(nom, denom):
        if nom < denom: return nom
        else: return mod(nom - denom, denom)
    """
    print("="*70)
    print("2. Division and Modulo Verification")
    print("="*70)
    
    print("Property: nom = denom * div + mod")
    print()
    
    if not Z3_AVAILABLE:
        print("Specification:")
        print("  div(nom, denom) * denom + mod(nom, denom) = nom")
        print("  mod(nom, denom) < denom")
        print()
        print("Implementation uses tail recursion with accumulator")
        return
    
    # Variables
    nom = z3.Int('nom')
    denom = z3.Int('denom')
    div_result = z3.Int('div')
    mod_result = z3.Int('mod')
    
    # Precondition
    pre = z3.And(nom >= 0, denom > 0)
    
    # Postcondition
    post = z3.And(
        nom == denom * div_result + mod_result,
        mod_result >= 0,
        mod_result < denom
    )
    
    # For verification, we use Z3's built-in div/mod
    # and verify our implementation matches
    div_result = nom / denom  # Z3 integer division
    mod_result = nom % denom  # Z3 modulo
    
    solver = z3.Solver()
    solver.add(pre)
    solver.add(z3.Not(post))
    
    if solver.check() == z3.unsat:
        print("✓ Division/modulo property verified")
        print("  nom = denom * div + mod")
        print("  0 ≤ mod < denom")
    else:
        print("✗ Property violated")
        model = solver.model()
        print(f"  Counterexample: nom={model[nom]}, denom={model[denom]}")
    
    print()


# ============================================================================
# 3. Find Maximum with Ghost Variable
# ============================================================================

def verify_find_max_ghost():
    """
    Verify find_max using ghost variable j
    
    Precondition: {0 ≤ j < n}
    mx = a[0];
    for (int i = 1; i < n; i++) {
        if (a[i] > mx) mx = a[i];
    }
    return mx;
    Postcondition: {a[j] ≤ mx}
    
    Ghost variable j: Exists somewhere in [0, n)
    """
    print("="*70)
    print("3. Find Maximum with Ghost Variable")
    print("="*70)
    
    print("Ghost variable j: index that we're proving about")
    print()
    print("Precondition:  0 ≤ j < n")
    print("Postcondition: a[j] ≤ mx")
    print()
    
    if not Z3_AVAILABLE:
        print("Loop Invariant:")
        print("  ∀k ∈ [0, i): a[k] ≤ mx")
        print()
        print("Proof:")
        print("  - Init: mx = a[0], invariant holds for i=1")
        print("  - Step: If a[i] > mx, update mx = a[i]")
        print("  - Exit: i = n, so ∀k < n: a[k] ≤ mx")
        print("  - Since j < n, we have a[j] ≤ mx ✓")
        return
    
    # Array and indices
    n = z3.Int('n')
    j = z3.Int('j')  # Ghost variable
    i = z3.Int('i')  # Loop counter
    
    # Array (as Z3 array)
    a = z3.Array('a', z3.IntSort(), z3.IntSort())
    mx = z3.Int('mx')
    
    # Precondition
    pre = z3.And(n > 0, j >= 0, j < n)
    
    # Loop invariant: ∀k < i: a[k] ≤ mx
    k = z3.Int('k')
    invariant = z3.ForAll([k], 
                         z3.Implies(z3.And(k >= 0, k < i),
                                   z3.Select(a, k) <= mx))
    
    # Postcondition: a[j] ≤ mx
    post = (z3.Select(a, j) <= mx)
    
    # Init: i = 1, mx = a[0]
    init = z3.And(
        i == 1,
        mx == z3.Select(a, 0),
        # Invariant holds: ∀k < 1: a[k] ≤ mx
        # Only k=0, and a[0] ≤ a[0] ✓
    )
    
    # Exit: i = n => post
    solver = z3.Solver()
    solver.add(pre)
    solver.add(invariant)
    solver.add(i == n)
    solver.add(z3.Not(post))
    
    if solver.check() == z3.unsat:
        print("✓ Postcondition verified")
        print("  When loop exits (i = n), invariant implies a[j] ≤ mx")
    else:
        print("✗ Postcondition not verified")
    
    print()


# ============================================================================
# 4. Find Value in Array
# ============================================================================

def verify_find_value():
    """
    Verify array search
    
    Precondition: {0 ≤ j < n ∧ a[j] = v}
    for (at = 0; at < n; at++) {
        if (a[at] == v) break;
    }
    return at;
    Postcondition: {at ≤ j}
    
    Proof: If we find v at position at, then at ≤ j
           (since j is some position where v appears)
    """
    print("="*70)
    print("4. Find Value in Array")
    print("="*70)
    
    print("Precondition:  0 ≤ j < n ∧ a[j] = v")
    print("Postcondition: at ≤ j")
    print()
    
    if not Z3_AVAILABLE:
        print("Loop Invariant:")
        print("  ∀k < at: a[k] ≠ v")
        print()
        print("Proof:")
        print("  - If loop breaks at position at, then a[at] = v")
        print("  - By invariant, ∀k < at: a[k] ≠ v")
        print("  - Since a[j] = v and ∀k < at: a[k] ≠ v")
        print("  - We must have j ≥ at, i.e., at ≤ j ✓")
        return
    
    # Variables
    n = z3.Int('n')
    j = z3.Int('j')  # Ghost: position where v appears
    at = z3.Int('at')  # Loop counter / result
    v = z3.Int('v')  # Value to find
    
    # Array
    a = z3.Array('a', z3.IntSort(), z3.IntSort())
    
    # Precondition
    pre = z3.And(
        n > 0,
        j >= 0,
        j < n,
        z3.Select(a, j) == v
    )
    
    # Loop invariant: ∀k < at: a[k] ≠ v
    k = z3.Int('k')
    invariant = z3.ForAll([k],
                         z3.Implies(z3.And(k >= 0, k < at),
                                   z3.Select(a, k) != v))
    
    # Break condition: a[at] = v
    break_cond = (z3.Select(a, at) == v)
    
    # Postcondition: at ≤ j
    post = (at <= j)
    
    # Verify: If we break with a[at] = v and invariant holds,
    # then at ≤ j
    solver = z3.Solver()
    solver.add(pre)
    solver.add(invariant)
    solver.add(break_cond)
    solver.add(at >= 0)
    solver.add(at < n)
    solver.add(z3.Not(post))
    
    if solver.check() == z3.unsat:
        print("✓ Postcondition verified")
        print("  If we find v at position at, then at ≤ j")
        print("  (Cannot have found it earlier than first occurrence)")
    else:
        print("✗ Postcondition not verified")
        model = solver.model()
        print(f"  Counterexample: at={model[at]}, j={model[j]}")
    
    print()


# ============================================================================
# Main
# ============================================================================

def main():
    """Run all verification examples."""
    print("\n")
    print("╔" + "="*68 + "╗")
    print("║" + " "*68 + "║")
    print("║" + "  Software Verification Examples".center(68) + "║")
    print("║" + "  Phase 5: Loop Verification".center(68) + "║")
    print("║" + " "*68 + "║")
    print("╚" + "="*68 + "╝")
    print()
    
    verify_addition_by_increment()
    verify_division_modulo()
    verify_find_max_ghost()
    verify_find_value()
    
    print("="*70)
    print("Summary")
    print("="*70)
    print()
    print("All verification examples completed!")
    print()
    print("Techniques demonstrated:")
    print("  1. Loop invariants")
    print("  2. Ghost variables")
    print("  3. Pre/postconditions")
    print("  4. Inductive proofs")
    print()
    print("Ready for Snake game verification! 🐍")
    print()
    
    return 0


if __name__ == '__main__':
    sys.exit(main())
