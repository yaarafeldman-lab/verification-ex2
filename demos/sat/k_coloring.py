"""
Example of reduction from k-coloring of a graph to SAT
"""

from z3 import *

# Petersen graph
Petersen_V = list(range(10))
Petersen_E = [
    (0 , 1),
    (1 , 2),
    (2 , 3),
    (3 , 4),
    (4 , 0),

    (0 , 5),
    (1 , 6),
    (2 , 7),
    (3 , 8),
    (4 , 9),

    (5 , 7),
    (7 , 9),
    (9 , 6),
    (6 , 8),
    (8 , 5),
 ]

# A simple graph
simple_V = [0, 1, 2, 3]
simple_E = [
    (0, 1),
    (1, 2),
    (2, 0),
    (2, 3),
]

def get_k_coloring(k, V, E):
    assert V == list(range(len(V)))
    colors = list(range(k))
    variables = [[Bool('v_{}_color_{}'.format(v, c)) for c in colors] for v in V]

    s = Solver()

    # every node has at least one color
    for v in V:
        s.add(Or([variables[v][c] for c in colors]))

    # every node has at most one color
    for v in V:
        for c1 in range(k):
            for c2 in range(c1 + 1, k):
                s.add(Or(Not(variables[v][c1]),
                         Not(variables[v][c2])))

    # every edge connects nodes with different colors
    for v1, v2 in E:
        for c in colors:
            s.add(Or(Not(variables[v1][c]),
                     Not(variables[v2][c])))

    # print("Solver is:")
    # print(s)
    # print()

    print("Checking SAT")
    res = s.check()
    if res == unsat:
        print("UNSAT, No K coloring")
        return None
    elif res == unknown:
        print("Unknown")
        return None
    else:
        assert res == sat
        print("SAT, Found K coloring")
        m = s.model()
        coloring = dict()
        for v in V:
            for c in colors:
                if is_true(m[variables[v][c]]):
                    coloring[v] = c
                    break
        return coloring


def draw_graph(V, E, coloring={}, filename='graph', engine='circo', directed=False):
    if c is None:
        return
    try:
        from graphviz import Graph, Digraph
    except ImportError:
        print("You don't have graphviz python interface installed. Sorry.")
        return

    COLORS = ['blue', 'red', 'green', 'pink', 'yellow']
    if directed:
        dot = Digraph(engine=engine)
    else:
        dot = Graph(engine=engine)
    for v in V:
        if v in coloring:
            dot.node(str(v), style="filled", fillcolor=COLORS[coloring[v]])
        else:
            dot.node(str(v))
    for v1, v2 in E:
        if (v1, v2) in coloring:
            dot.edge(str(v1), str(v2), color=COLORS[coloring[(v1, v2)]])
        else:
            dot.edge(str(v1), str(v2))
    dot.render(filename, cleanup=True)


if __name__ == '__main__':
    print("Simple graph (3 colors):")
    c = get_k_coloring(3, simple_V, simple_E)
    print(c)
    draw_graph(simple_V, simple_E, c, 'simple-3')
    print()

    print("Simple graph (2 colors):")
    c = get_k_coloring(2, simple_V, simple_E)
    print(c)
    draw_graph(simple_V, simple_E, c, 'simple-2')
    print()


    print("Petersen graph (3 colors):")
    c = get_k_coloring(3, Petersen_V, Petersen_E)
    print(c)
    draw_graph(Petersen_V, Petersen_E, c, 'Petersen-3')
    print()

    print("Petersen graph (2 colors):")
    c = get_k_coloring(2, Petersen_V, Petersen_E)
    print(c)
    draw_graph(Petersen_V, Petersen_E, c, 'Petersen-2')
    print()
