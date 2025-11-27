# Arithmetic Circuits

This directory contains parametric arithmetic circuit designs and their formal verification.

## Files

- **`adder.py`**: Parametric k-bit adder implementation
  - `make_adder(k)`: Creates a k-bit adder (truncated output)
  - `make_adder_with_carry(k)`: Creates a k-bit adder with carry output

- **`verify_adder.py`**: Command-line verification script
  - Verifies adder correctness using Z3 SMT solver
  - Benchmarks verification time for different bit widths
  - Generates performance plots

- **`verify_adder.ipynb`**: Interactive Jupyter notebook
  - Step-by-step adder verification walkthrough
  - Visualization of verification results
  - Analysis of verification time complexity

## Usage

### Quick Test
```bash
python3 verify_adder.py
```

### Interactive Exploration
```bash
jupyter lab verify_adder.ipynb
```

## Requirements

- PyRTL
- Z3 Python bindings
- matplotlib (for plotting)
- pandas (for tables)

## Warmup Exercise

As described in the course slides, the warmup exercise involves:

1. **Implementing `net_to_smt`** ✓
   - Located in `../base/circuit.py`
   - Translates PyRTL circuits to Z3 SMT formulas

2. **Creating a parametric k-bit adder** ✓
   - Implemented in `adder.py`
   - Width is configurable via parameter k

3. **Verifying the adder** ✓
   - Uses `net_to_smt` to translate circuit
   - Z3 proves correctness by finding no counterexamples

4. **Benchmarking** ✓
   - Measures verification time vs. bit width k
   - Generates plots showing performance characteristics
