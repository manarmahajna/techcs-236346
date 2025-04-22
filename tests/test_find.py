from hw.cpu.simulate.simulation_utils import simulate_file

def test_find_present():
    result = simulate_file("sw/basics/find.sasm", data=[4, 8, 12, 3], extra_stack=[4, 12])
    assert result == 2

def test_find_not_present():
    result = simulate_file("sw/basics/find.sasm", data=[1, 2, 3], extra_stack=[3, 9])
    assert result == 3
