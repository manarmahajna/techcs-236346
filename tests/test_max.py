from hw.cpu.simulate.simulation_utils import simulate_file

def test_max_basic():
    result = simulate_file("sw/basics/max.sasm", data=[3, 7, 2, 9, 5], extra_stack=[5])
    assert result == 9

def test_max_negative_numbers():
    result = simulate_file("sw/basics/max.sasm", data=[-4, -2, -10, -1], extra_stack=[4])
    assert result == -1
