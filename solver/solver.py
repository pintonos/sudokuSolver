import sys

from z3 import *


def all9(vs):
    assert (len(vs) == 9)
    return Distinct(vs)


def solve(A):
    vars = [[Int(str(i) + str(j)) for j in range(9)] for i in range(9)]

    solver = Solver()

    for r in vars:
        for v in r:
            solver.add(1 <= v, v <= 9)

    # predefined values
    for i, row in enumerate(A):
        for j, val in enumerate(row):
            if val > 0:
                solver.add(vars[i][j] == val)

    # condition elements 1 .. 9 in rows and columns
    for j in range(9):
        solver.add(all9(vars[j]))
        solver.add(all9([vars[i][j] for i in range(9)]))

        # determine block
        br = j % 3
        bc = j / 3
        bs = [vars[3 * br + k][3 * bc + l] for k in range(3) for l in range(3)]
        solver.add(all9(bs))

    result = solver.check()  # check for satisfiability
    if result == z3.sat:
        model = solver.model()  # get valuation
        for row in vars:
            print(reduce(lambda s, v: s + str(model[v]) + " ", row, ""))
    else:
        print("no solution found")


def readProblem(fname):
    A = []
    with open(fname) as f:
        for l in f.readlines():
            row = [int(c) for c in l.strip().split(' ') if c]
            assert (len(row) == 9)
            A.append(row)
    assert (len(A) == 9)
    return A


if len(sys.argv) < 2:
    print("usage: solver.py <input file>")
    exit

A = readProblem(sys.argv[1])
solve(A)
