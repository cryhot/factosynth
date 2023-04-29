#!/usr/bin/env python3
import sys
import os
import pytest
from termcolor import colored, cprint

sys.path.append(os.path.join(os.path.dirname(__file__),os.path.pardir))
import z3
from factosynth import (
    Int32Sort,
    Operator, Comparator, Operation,
    Register,
    EACH, ANYTHING, EVERYTHING,
    DeciderControlBehavior,
    ArithmeticControlBehavior,
)



a = z3.Const(f'COUNT:a', Int32Sort)
b = z3.Const(f'COUNT:b', Int32Sort)
c = z3.Const(f'COUNT:c', Int32Sort)

@pytest.mark.parametrize("control_behavior, input, output", [
    *(pytest.param(DeciderControlBehavior('A', '≥', 'B', 'C', True), I, O, id="Decider-Simple-IO") for I, O in [
        (Register(C=c), Register(C=c)),
        (Register(A=4, B=5, C=c), Register()),
        (Register(A=6, B=5, C=c), Register(C=c)),
    ]),
    *(pytest.param(DeciderControlBehavior('A', '≥', 'B', 'C', False), I, O, id="Decider-SimpleThen1-IO") for I, O in [
        (Register(C=c), Register(C=1)),
        (Register(A=4, B=5, C=c), Register()),
        (Register(A=6, B=5, C=c), Register(C=1)),
    ]),
    *(pytest.param(DeciderControlBehavior('A', '≥', 'B', EVERYTHING, True), I, O, id="Decider-SimpleThenEverything-IO") for I, O in [
        (Register(C=c), Register(C=c)),
        (Register(A=4, B=5, C=c), Register()),
        (Register(A=6, B=5, C=c), Register(A=6, B=5, C=c)),
    ]),
    *(pytest.param(DeciderControlBehavior('A', '≥', 'B', EVERYTHING, False), I, O, id="Decider-SimpleThen1AsEverything-IO") for I, O in [
        (Register(C=c), Register(C=z3.If(c!=0,Int32Sort.cast(1),Int32Sort.cast(0)))),
        (Register(A=4, B=5, C=c), Register()),
        (Register(A=6, B=5, C=c), Register(A=1, B=1, C=z3.If(c!=0,Int32Sort.cast(1),Int32Sort.cast(0)))),
    ]),

    *(pytest.param(DeciderControlBehavior(EVERYTHING, '>', 0, 'C', True), I, O, id="Decider-Everything-IO") for I, O in [
        (Register(A=5, C=3), Register(C=3)),
        (Register(A=-5, C=3), Register()),
    ]),
    *(pytest.param(DeciderControlBehavior(EVERYTHING, '>', 0, 'C', False), I, O, id="Decider-EverythingThen1-IO") for I, O in [
        (Register(A=5, C=3), Register(C=1)),
        (Register(A=-5, C=3), Register()),
    ]),
    *(pytest.param(DeciderControlBehavior(EVERYTHING, '>', 0, EVERYTHING, True), I, O, id="Decider-EverythingThenEverything-IO") for I, O in [
        (Register(A=5, C=3), Register(A=5, C=3)),
        (Register(A=-5, C=3), Register()),
    ]),
    *(pytest.param(DeciderControlBehavior(EVERYTHING, '>', 0, EVERYTHING, False), I, O, id="Decider-EverythingThen1AsEverything-IO") for I, O in [
        (Register(A=5, C=3), Register(A=1, C=1)),
        (Register(A=-5, C=3), Register()),
    ]),

    *(pytest.param(DeciderControlBehavior(ANYTHING, '≤', 0, 'C', True), I, O, id="Decider-Anything-IO") for I, O in [
        (Register(A=5, C=3), Register()),
        (Register(A=-5, C=3), Register(C=3)),
    ]),
    *(pytest.param(DeciderControlBehavior(ANYTHING, '≤', 0, 'C', False), I, O, id="Decider-AnythingThen1-IO") for I, O in [
        (Register(A=5, C=3), Register()),
        (Register(A=-5, C=3), Register(C=1)),
    ]),
    *(pytest.param(DeciderControlBehavior(ANYTHING, '≤', 0, EVERYTHING, True), I, O, id="Decider-AnythingThenEverything-IO") for I, O in [
        (Register(A=5, C=3), Register()),
        (Register(A=-5, C=3), Register(A=-5, C=3)),
    ]),
    *(pytest.param(DeciderControlBehavior(ANYTHING, '≤', 0, EVERYTHING, False), I, O, id="Decider-AnythingThen1AsEverything-IO") for I, O in [
        (Register(A=5, C=3), Register()),
        (Register(A=-5, C=3), Register(A=1, C=1)),
    ]),
    *(pytest.param(DeciderControlBehavior(ANYTHING, '≤', 0, ANYTHING, True), I, O, id="Decider-AnythingThenChoice-IO") for I, O in [
        (Register(A=5, C=3), Register()),
        (Register(A=-5, C=3), Register(A=-5)),
        (Register(A=-5, B=-2, C=3), Register(A=-5)), # assuming that A comes first
    ]),
    *(pytest.param(DeciderControlBehavior(ANYTHING, '≤', 0, ANYTHING, False), I, O, id="Decider-AnythingThen1AsChoice-IO") for I, O in [
        (Register(A=5, C=3), Register()),
        (Register(A=-5, C=3), Register(A=1)),
        (Register(A=-5, B=-2, C=3), Register(A=1)), # assuming that A comes first
    ]),
    
    *(pytest.param(DeciderControlBehavior(EACH, '≥', 'B', EACH, True), I, O, id="Decider-EachThenEach-IO") for I, O in [
        (Register(C=c), Register(C=z3.If(c>0,c,0))),
        (Register(A=5, B=4, C=3), Register(A=5, B=4)),
    ]),
    *(pytest.param(DeciderControlBehavior(EACH, '≥', 'B', EACH, False), I, O, id="Decider-EachThen1AsEach-IO") for I, O in [
        (Register(C=c), Register(C=z3.If(c>0,Int32Sort.cast(1),Int32Sort.cast(0)))),
        (Register(A=5, B=4, C=3), Register(A=1, B=1)),
    ]),
    *(pytest.param(DeciderControlBehavior(EACH, '≥', 'B', 'C', True), I, O, id="Decider-EachThenSum-IO") for I, O in [
        (Register(C=c), Register(C=z3.If(c>0,c,0))),
        (Register(A=5, B=4, C=3), Register(C=9)),
    ]),
    *(pytest.param(DeciderControlBehavior(EACH, '≥', 'B', 'C', False), I, O, id="Decider-EachThenCount-IO") for I, O in [
        (Register(C=c), Register(C=z3.If(c>0,Int32Sort.cast(1),Int32Sort.cast(0)))),
        (Register(A=5, B=4, C=3), Register(C=2)),
    ]),
    

    *(pytest.param(ArithmeticControlBehavior('A', '*', 'B', 'C'), I, O, id="Arithmetic-Simple-IO") for I, O in [
        (Register(A=7, B=8, C=c), Register(C=56)),
    ]),
    *(pytest.param(ArithmeticControlBehavior('A', '%', 'B', 'C'), I, O, id="Arithmetic-Modulo-IO") for I, O in [
        (Register(A= 12, B= 10), Register(C= 2)),
        (Register(A=-12, B= 10), Register(C=-2)),
        (Register(A= 12, B=-10), Register(C= 2)),
        (Register(A=-12, B=-10), Register(C=-2)),
    ]),
    *(pytest.param(ArithmeticControlBehavior(EACH, '*', -1, EACH), I, O, id="Arithmetic-EachAsEach-IO") for I, O in [
        (Register(A=a, B=b, C=c), Register(A=-a, B=-b, C=-c)),
    ]),
    *(pytest.param(ArithmeticControlBehavior(0, '-', EACH, EACH), I, O, id="Arithmetic-REachAsEach-IO") for I, O in [
        (Register(A=a, B=b, C=c), Register(A=-a, B=-b, C=-c)),
    ]),
    *(pytest.param(ArithmeticControlBehavior(EACH, '*', -1, 'C'), I, O, id="Arithmetic-EachAsSum-IO") for I, O in [
        (Register(A=a, B=b, C=c), Register(C=-a-b-c)),
    ]),
    *(pytest.param(ArithmeticControlBehavior(0, '-', EACH, 'C'), I, O, id="Arithmetic-REachAsEach-IO") for I, O in [
        (Register(A=a, B=b, C=c), Register(C=-a-b-c)),
    ]),
])
def test_control_behavior_semantics(control_behavior, input, output):
    """Checks that control behaviors behave as expected."""
    signals = ['A','B','C']
    for signal in signals:
        input.setdefault(signal,0)
        output.setdefault(signal,0)

    ans = control_behavior(input)

    print(f"""{input} {colored("->",color='blue')} {control_behavior.to_cnide()} {colored("->",color='blue')} {ans}""")
    is_expected = ans==output
    m = None
    if not isinstance(is_expected, bool):
        cprint("Checking output requires solving a SAT problem.", color='yellow', attrs=['bold'])
        solver = z3.Solver()
        solver.set(timeout=int(min(1*1000, sys.maxsize)))
        solver.add(z3.Not(is_expected))
        check = solver.check()
        if check == z3.unsat:
            cprint("That was expected! Expecting:", color='green', attrs=['bold'])
            cprint(f"""{input} -> {control_behavior.to_cnide()} -> {output}""", color='yellow')
            is_expected = True
        elif check == z3.sat:
            is_expected = False
        else:
            cprint("Could not check correctness of output! Expecting:", color='red', attrs=['bold'])
            cprint(f"""{input} -> {control_behavior.to_cnide()} -> {output}""", color='yellow')
            m = "cannot check correctness of output"
    if not is_expected:
        cprint("That was unexpected! Expecting:", color='red', attrs=['bold'])
        cprint(f"""{input} -> {control_behavior.to_cnide()} -> {output}""", color='yellow')
        m = "unexpected output"
    if m:
        pytest.fail(
            f"{m.capitalize()}.",
            pytrace=False,
        )



# @pytest.fixture
def operations():
    return [op for op in Operation.operators if op not in ['^']]
    # the power operator is expansive to synthesize, since it is not a standard bitvector operator.

# @pytest.fixture
def signals():
    return ['A', 'B', 'C']

@pytest.mark.parametrize("control_behavior_sketch, IO_examples", [
    pytest.param(
        DeciderControlBehavior(signals=signals()),
        # expected = DeciderControlBehavior('A', '≥', 'B', 'C', True)
        [
            (Register(C=1), Register(C=1)),
            (Register(A=4,B=5,C=3), Register()),
            (Register(A=3,B=6,C=7), Register()),
            (Register(A=6,B=5,C=3), Register(C=3)),
        ],
        id = "Decider-SimpleThreshold"
    ),
    pytest.param(
        ArithmeticControlBehavior(operation=operations(), signals=signals()),
        # expected = DeciderControlBehavior('A', '/', 5, 'C')
        [
            (Register(A=5), Register(C=1)),
            (Register(A=20), Register(C=4)),
            (Register(A=35), Register(C=7)),
        ],
        id = "Decider-SimpleDivision"
    ),
    pytest.param(
        ArithmeticControlBehavior(operation=operations(), signals=signals()),
        # expected = DeciderControlBehavior(0, '+', EACH, 'C')
        [
            (Register(A=3, B=6, C=1), Register(C=10)),
            (Register(A=1, B=1, C=1), Register(C=3)),
        ],
        id = "Arithmetic-sum"
    ),
])
def test_control_behavior_synthesis(control_behavior_sketch, IO_examples):
    """Check the capabilities of behavior synthesis."""
    solver = z3.Solver()
    solver.add(control_behavior_sketch.valid)
    for input, output in IO_examples:
        for signal in signals():
            input.setdefault(signal,0)
            output.setdefault(signal,0)
        ans = control_behavior_sketch(input)
        solver.add(ans == output)

    import time
    start_t = time.perf_counter()
    check = solver.check()
    elapsed_t = time.perf_counter() - start_t
    cprint(f"Solve SAT: {elapsed_t:.3f}s elsapsed.", color='magenta', attrs=['bold'])

    assert check == z3.sat, f"solution is {check}"
    model = solver.model()
    control_behavior = control_behavior_sketch.eval(model)
    # print(model)

    print(control_behavior.to_cnide())
    for input, output in IO_examples:
        ans = control_behavior(input)
        test_control_behavior_semantics(control_behavior, input, output)
        # print(f"""{input} {colored("->",color='blue')} {control_behavior.to_cnide()} {colored("->",color='blue')} {ans}""")
        # assert ans == output



if __name__ == "__main__":
    # invokes `python3 -m pytest`
    sys.exit(pytest.main([
        __file__,
        # f"{__file__}::test_control_behavior_semantics[Decider-EachThenEach-IO0]",
        # f"{__file__}::test_control_behavior_synthesis",
        '-rP', # Show passed tests outputs
        # '-s',  # Show Output, do not capture
    ]))
