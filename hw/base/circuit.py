"""
Translation from PyRTL circuits to Z3 SMT formulas.
"""
import z3
from collections import namedtuple


class WireDict:
    """Dictionary-like object for looking up Z3 variables by wire name."""
    def __init__(self):
        self._wires = {}
    
    def __setitem__(self, name, var):
        self._wires[name] = var
    
    def __getitem__(self, name):
        return self._wires[name]
    
    def lookup(self, name):
        """Look up a wire by name."""
        return self._wires[name]
    
    def items(self):
        return self._wires.items()


def net_to_smt(block, mems=None):
    """
    Translate a PyRTL block to Z3 SMT formulas.
    
    Args:
        block: PyRTL working block containing the circuit
        mems: Optional list of memory blocks to handle
    
    Returns:
        tuple: (wires, ops, assertions)
            - wires: WireDict mapping wire names to Z3 BitVec variables
            - ops: list of operations (for debugging/inspection)
            - assertions: list of Z3 formulas constraining the circuit behavior
    """
    mems = mems or []
    wires = WireDict()
    ops = []
    assertions = []
    
    # Create Z3 variables for all wires
    for net in block:
        # Create variables for destination wires
        for dest in net.dests:
            if dest.name not in wires._wires:
                wires[dest.name] = z3.BitVec(dest.name, dest.bitwidth)
        
        # Create variables for argument wires
        for arg in net.args:
            if arg.name not in wires._wires:
                wires[arg.name] = z3.BitVec(arg.name, arg.bitwidth)
    
    # Create Z3 variables for memory blocks
    mem_vars = {}
    for mem in mems:
        mem_vars[mem.name] = z3.Array(mem.name, 
                                       z3.BitVecSort(mem.addrwidth), 
                                       z3.BitVecSort(mem.bitwidth))
    
    # Generate constraints for each operation
    for net in block:
        op = net.op
        args = [wires[arg.name] for arg in net.args]
        dest = wires[net.dests[0].name] if net.dests else None
        
        ops.append((op, net.op_param, [arg.name for arg in net.args], 
                   [d.name for d in net.dests]))
        
        if op == 'w':  # Wire (assignment)
            assertions.append(dest == args[0])
        
        elif op == '&':  # Bitwise AND
            assertions.append(dest == (args[0] & args[1]))
        
        elif op == '|':  # Bitwise OR
            assertions.append(dest == (args[0] | args[1]))
        
        elif op == '^':  # Bitwise XOR
            assertions.append(dest == (args[0] ^ args[1]))
        
        elif op == '~':  # Bitwise NOT
            assertions.append(dest == ~args[0])
        
        elif op == '+':  # Addition
            result = args[0] + args[1]
            # Truncate to destination width if needed
            dest_width = net.dests[0].bitwidth
            if dest_width < result.size():
                result = z3.Extract(dest_width - 1, 0, result)
            assertions.append(dest == result)
        
        elif op == '-':  # Subtraction
            result = args[0] - args[1]
            dest_width = net.dests[0].bitwidth
            if dest_width < result.size():
                result = z3.Extract(dest_width - 1, 0, result)
            assertions.append(dest == result)
        
        elif op == '*':  # Multiplication
            result = args[0] * args[1]
            dest_width = net.dests[0].bitwidth
            if dest_width < result.size():
                result = z3.Extract(dest_width - 1, 0, result)
            assertions.append(dest == result)
        
        elif op == 's':  # Select (bit extraction)
            bit_index = net.op_param[0]
            assertions.append(dest == z3.Extract(bit_index, bit_index, args[0]))
        
        elif op == 'c':  # Concat (concatenation)
            # Concatenate from left to right (MSB to LSB)
            result = args[0]
            for arg in args[1:]:
                result = z3.Concat(result, arg)
            assertions.append(dest == result)
        
        elif op == 'r':  # Register (state element)
            # For combinational verification, treat as a wire
            # For sequential, this needs special handling
            if len(args) > 0:
                assertions.append(dest == args[0])
        
        elif op == 'x':  # Mux (multiplexer)
            # args[0] is select, args[1] is false value, args[2] is true value
            select = args[0]
            false_val = args[1]
            true_val = args[2]
            assertions.append(dest == z3.If(select != 0, true_val, false_val))
        
        elif op == '<':  # Less than (unsigned)
            assertions.append(dest == z3.If(z3.ULT(args[0], args[1]), 
                                            z3.BitVecVal(1, 1), 
                                            z3.BitVecVal(0, 1)))
        
        elif op == '>':  # Greater than (unsigned)
            assertions.append(dest == z3.If(z3.UGT(args[0], args[1]), 
                                            z3.BitVecVal(1, 1), 
                                            z3.BitVecVal(0, 1)))
        
        elif op == '=':  # Equal
            assertions.append(dest == z3.If(args[0] == args[1], 
                                            z3.BitVecVal(1, 1), 
                                            z3.BitVecVal(0, 1)))
        
        elif op == 'm':  # Memory read
            mem_name = net.op_param[0]
            addr = args[0]
            mem = mem_vars[mem_name]
            assertions.append(dest == z3.Select(mem, addr))
        
        elif op == '@':  # Memory write
            mem_name = net.op_param[0]
            addr = args[0]
            data = args[1]
            old_mem = mem_vars[mem_name]
            assertions.append(dest == z3.Store(old_mem, addr, data))
        
        # Add more operations as needed
    
    return wires, ops, assertions

