"""
Verify the parametric k-bit adder using Z3.
"""
import sys
import time
sys.path.insert(0, '../base')

import pyrtl
from pyrtl import *
import z3
from circuit import net_to_smt
from adder import make_adder


def verify_adder(k, verbose=False):
    """
    Verify that the k-bit adder correctly implements addition.
    
    Args:
        k: bit width of the adder
        verbose: if True, print detailed information
    
    Returns:
        tuple: (verification_result, time_taken_seconds)
    """
    if verbose:
        print(f"\n{'='*60}")
        print(f"Verifying {k}-bit adder...")
        print(f"{'='*60}")
    
    # Create the adder circuit
    a, b, sum_out = make_adder(k)
    wb = pyrtl.working_block()
    
    if verbose:
        print(f"Circuit has {len(list(wb))} nets")
    
    # Convert to SMT
    start_time = time.time()
    wires, ops, assertions = net_to_smt(wb)
    
    # Create Z3 solver
    solver = z3.Solver()
    
    # Add circuit constraints
    for assertion in assertions:
        solver.add(assertion)
    
    # The property we want to verify:
    # For all inputs a, b: sum == (a + b) mod 2^k
    # 
    # We verify this by trying to find a counterexample.
    # If no counterexample exists, the adder is correct.
    
    a_var = wires.lookup('a')
    b_var = wires.lookup('b')
    sum_var = wires.lookup('sum')
    
    # Create the correctness property
    # sum should equal (a + b) truncated to k bits
    expected_sum = z3.Extract(k-1, 0, a_var + b_var)
    correctness = (sum_var == expected_sum)
    
    # Try to find a counterexample (negation of correctness)
    solver.add(z3.Not(correctness))
    
    result = solver.check()
    elapsed_time = time.time() - start_time
    
    if verbose:
        print(f"\nVerification result: {result}")
        print(f"Time taken: {elapsed_time:.4f} seconds")
    
    if result == z3.unsat:
        if verbose:
            print(f"✓ The {k}-bit adder is CORRECT!")
        return True, elapsed_time
    elif result == z3.sat:
        if verbose:
            print(f"✗ The {k}-bit adder is INCORRECT!")
            print("Counterexample:")
            model = solver.model()
            print(f"  a = {model.eval(a_var)}")
            print(f"  b = {model.eval(b_var)}")
            print(f"  sum = {model.eval(sum_var)}")
            print(f"  expected = {model.eval(expected_sum)}")
        return False, elapsed_time
    else:
        if verbose:
            print(f"? Verification UNKNOWN: {solver.reason_unknown()}")
        return None, elapsed_time


def benchmark_verification(k_values):
    """
    Benchmark verification time for different values of k.
    
    Args:
        k_values: list of k values to test
    
    Returns:
        tuple: (k_values, times, results)
    """
    print("Benchmarking adder verification...")
    print(f"Testing k values: {k_values}")
    print()
    
    times = []
    results = []
    
    for k in k_values:
        print(f"k={k:2d}... ", end='', flush=True)
        result, elapsed = verify_adder(k, verbose=False)
        times.append(elapsed)
        results.append(result)
        
        status = "✓" if result else ("✗" if result is False else "?")
        print(f"{status} {elapsed:6.3f}s")
    
    print("\nBenchmark complete!")
    return k_values, times, results


if __name__ == "__main__":
    # Test a single adder first
    print("="*60)
    print("Testing 4-bit adder verification")
    print("="*60)
    verify_adder(4, verbose=True)
    
    # Benchmark multiple values of k
    print("\n\n")
    k_values = [1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 16, 20, 24, 32]
    
    ks, times, results = benchmark_verification(k_values)
    
    # Print summary table
    print("\n" + "="*60)
    print("Summary:")
    print("="*60)
    print(f"{'k':<5} {'Time (s)':<12} {'Result':<10}")
    print("-"*60)
    for k, t, r in zip(ks, times, results):
        status = "CORRECT" if r else ("INCORRECT" if r is False else "UNKNOWN")
        print(f"{k:<5} {t:<12.4f} {status:<10}")
    
    # Try to plot if matplotlib is available
    try:
        import matplotlib.pyplot as plt
        
        plt.figure(figsize=(10, 6))
        plt.plot(ks, times, 'o-', linewidth=2, markersize=8)
        plt.xlabel('Bit Width (k)', fontsize=12)
        plt.ylabel('Verification Time (seconds)', fontsize=12)
        plt.title('Adder Verification Time vs. Bit Width', fontsize=14)
        plt.grid(True, alpha=0.3)
        plt.yscale('log')
        plt.tight_layout()
        plt.savefig('adder_verification_benchmark.png', dpi=150)
        print("\n✓ Plot saved to 'adder_verification_benchmark.png'")
        
        # Also show if in interactive mode
        # plt.show()
    except ImportError:
        print("\nNote: matplotlib not available. Install it to generate plots.")
        print("      pip install matplotlib")
