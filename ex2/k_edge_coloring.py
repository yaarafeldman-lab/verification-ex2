"""
k-edge-coloring exercise.
"""

from z3 import *

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

small_V = list(range(7))
small_E = [
    (0,1), (0,2), (0,3),   # the obstruction
    (4,5), (5,6)           # irrelevant
]


def get_k_edge_coloring(k, V, E):
    assert V == list(range(len(V)))
    edge_indices = range(len(E))
    colors = list(range(k))
    variables = [[Bool('e_{}_color_{}'.format(e, c)) for c in colors] for e in edge_indices]

    s = Solver()

    # every edge has a color
    for e in edge_indices:
        s.add(Or([variables[e][c] for c in colors]))

    # every node has at most one color
    for e in edge_indices:
        for c1 in range(k):
            for c2 in range(c1 + 1, k):
                s.add(Or(
                    Not(variables[e][c1]),
                    Not(variables[e][c2])
                ))

    # making sure that adjacent edges have different colors
    for i in edge_indices:
        for j in edge_indices[i+1:len(E)]:
            intersctn = set(E[i]) & set(E[j])
            if len(intersctn) == 1:
                for c in colors:
                    s.add(Or(
                            Not(variables[i][c]),
                            Not(variables[j][c])
                    ))
                


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
        for e in edge_indices:
            for c in colors:
                if is_true(m[variables[e][c]]):
                    coloring[E[e]] = c
                    break
        return coloring


def get_k_edge_coloring_core(k, V, E):
    assert V == list(range(len(V)))
    edge_indices = range(len(E))
    colors = list(range(k))
    variables = [[Bool('e_{}_color_{}'.format(e, c)) for c in colors] for e in edge_indices]

    s = Solver()

    # every edge has a color
    for e in edge_indices:
        s.add(Or([variables[e][c] for c in colors]))

    # every node has at most one color
    for e in edge_indices:
        for c1 in range(k):
            for c2 in range(c1 + 1, k):
                s.add(Or(
                    Not(variables[e][c1]),
                    Not(variables[e][c2])
                ))

    # making sure that adjacent edges have different colors
    edge_existence_vars = [Bool(str(i)) for i in edge_indices]
    for i in edge_indices:
        for j in edge_indices[i+1:len(E)]:
            intersctn = set(E[i]) & set(E[j])
            if len(intersctn) == 1:
                for c in colors:
                    s.add(Or(
                            Not(edge_existence_vars[i]),
                            Not(edge_existence_vars[j]),
                            Not(variables[i][c]),
                            Not(variables[j][c])
                    ))
                


    print("Checking SAT")
    res = s.check(edge_existence_vars)
    if res == unsat:
        print("UNSAT, No K coloring")
        core = s.unsat_core()
        print("UNSAT core:", core)
        coloring = dict()
        for x in core:
            i = int(str(x))
            coloring[E[i]] = 1
        return coloring
    elif res == unknown:
        print("Unknown")
        return None
    else:
        assert res == sat
        print("SAT, Found K coloring")
        m = s.model()
        coloring = dict()
        for e in edge_indices:
            for c in colors:
                if is_true(m[variables[e][c]]):
                    coloring[E[e]] = c
                    break
        return coloring



def draw_graph(V, E, coloring={}, filename='graph', engine='circo', directed=False):
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


def run_tests():
    tests = [
        {
            "name": "Single edge, k=1",
            "V": [0, 1],
            "E": [(0, 1)],
            "k": 1
        },
        {
            "name": "Path graph (0-1-2-3), k=2",
            "V": [0, 1, 2, 3],
            "E": [(0,1), (1,2), (2,3)],
            "k": 2
        },
        {
            "name": "4-cycle, k=2",
            "V": [0, 1, 2, 3],
            "E": [(0,1), (1,2), (2,3), (3,0)],
            "k": 2
        },
        {
            "name": "Triangle, k=2 (UNSAT)",
            "V": [0, 1, 2],
            "E": [(0,1), (1,2), (2,0)],
            "k": 2
        },
        {
            "name": "Triangle, k=3",
            "V": [0, 1, 2],
            "E": [(0,1), (1,2), (2,0)],
            "k": 3
        },
        {
            "name": "Star with 3 edges, k=2 (UNSAT)",
            "V": [0,1,2,3],
            "E": [(0,1), (0,2), (0,3)],
            "k": 2
        },
        {
            "name": "Disconnected graph, k=2",
            "V": [0,1,2,3,4,5],
            "E": [(0,1), (1,2), (3,4)],
            "k": 2
        },
        {
            "name": "Star + irrelevant edge, k=2 (core subset)",
            "V": [0,1,2,3,4,5],
            "E": [(0,1), (0,2), (0,3), (4,5)],
            "k": 2
        },
        {
            "name": "Triangle inside bigger graph, k=2 (core subset)",
            "V": list(range(8)),
            "E": [(0,1), (1,2), (2,0), (3,4), (4,5), (6,7)],
            "k": 2
        },
        {
            "name": "Petersen graph, k=3 (UNSAT, full core expected)",
            "V": list(range(10)),
            "E": [
                (0,1),(1,2),(2,3),(3,4),(4,0),
                (0,5),(1,6),(2,7),(3,8),(4,9),
                (5,7),(7,9),(9,6),(6,8),(8,5)
            ],
            "k": 3
        },
        {
            "name": "Petersen graph, k=4 (SAT)",
            "V": list(range(10)),
            "E": [
                (0,1),(1,2),(2,3),(3,4),(4,0),
                (0,5),(1,6),(2,7),(3,8),(4,9),
                (5,7),(7,9),(9,6),(6,8),(8,5)
            ],
            "k": 4
        }
    ]

    for t in tests:
        print("\n" + "#" * 60)
        print(t["name"])
        print("#" * 60)

        V, E, k = t["V"], t["E"], t["k"]

        print("\nget_k_edge_coloring:")
        res1 = get_k_edge_coloring(k, V, E)
        if res1:
            draw_graph(V, E, res1, f'coloring-{t["name"]}-{k}')

        print("\nget_k_edge_coloring_core:")
        res2 = get_k_edge_coloring_core(k, V, E)
        draw_graph(V, E, res2, f'coloring-or-core-{t["name"]}-{k}')


if __name__ == '__main__':
    run_tests()