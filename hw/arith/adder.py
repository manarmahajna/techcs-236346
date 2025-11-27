"""
Parametric k-bit adder implementation using PyRTL.
"""
import pyrtl
from pyrtl import *


def make_adder(k):
    """
    Create a k-bit adder circuit.
    
    Args:
        k: bit width of the adder inputs and output
    
    Returns:
        tuple: (a, b, sum) - the input and output wires
    """
    pyrtl.reset_working_block()
    
    a = pyrtl.Input(bitwidth=k, name='a')
    b = pyrtl.Input(bitwidth=k, name='b')
    sum_out = pyrtl.Output(bitwidth=k, name='sum')
    
    # Implement the adder - truncate to k bits
    sum_out <<= (a + b)[:k]
    
    return a, b, sum_out


def make_adder_with_carry(k):
    """
    Create a k-bit adder circuit with carry output.
    
    Args:
        k: bit width of the adder inputs
    
    Returns:
        tuple: (a, b, sum, carry) - the input and output wires
    """
    pyrtl.reset_working_block()
    
    a = pyrtl.Input(bitwidth=k, name='a')
    b = pyrtl.Input(bitwidth=k, name='b')
    sum_out = pyrtl.Output(bitwidth=k, name='sum')
    carry_out = pyrtl.Output(bitwidth=1, name='carry')
    
    # Compute full sum (k+1 bits)
    full_sum = a + b
    
    # Extract k-bit sum and carry
    sum_out <<= full_sum[:k]
    carry_out <<= full_sum[k]
    
    return a, b, sum_out, carry_out


if __name__ == "__main__":
    # Example: create and simulate a 4-bit adder
    print("Testing 4-bit adder:")
    a, b, sum_out = make_adder(4)
    
    # Simulate
    sim_trace = pyrtl.SimulationTrace()
    sim = pyrtl.Simulation(tracer=sim_trace)
    
    test_cases = [
        (0, 0),
        (5, 3),
        (15, 1),
        (7, 8),
        (15, 15),
    ]
    
    print("\nTest cases:")
    print("a + b = sum (expected)")
    for a_val, b_val in test_cases:
        sim.step({'a': a_val, 'b': b_val})
        result = sim.inspect('sum')
        expected = (a_val + b_val) % (2**4)
        status = "✓" if result == expected else "✗"
        print(f"{a_val:2d} + {b_val:2d} = {result:2d} ({expected:2d}) {status}")
    
    print("\nCircuit created successfully!")
