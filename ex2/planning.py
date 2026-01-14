"""
Transport planning problem exercise.
"""
from z3 import *


example_problem = dict(
    nc=4,
    np=3,
    na=2,
    src=[2,1,0],
    dst=[0,3,2],
    start=[3,3]
)


example_solution = dict(
    city_packages=[[[2], [1], [0], []],
                   [[2], [1], [0], []],
                   [[2], [], [], []],
                   [[2], [], [], []],
                   [[0], [], [], []],
                   [[0], [], [], []],
                   [[0], [], [2], [1]]],
    city_airplanes=[[[], [], [], [0, 1]],
                    [[], [0], [1], []],
                    [[], [0], [1], []],
                    [[0, 1], [], [], []],
                    [[1], [0], [], []],
                    [[], [], [1], [0]],
                    [[], [], [1], [0]]],
    airplane_packages=[[[], []],
                       [[], []],
                       [[1], [0]],
                       [[1], [0]],
                       [[1], [2]],
                       [[1], [2]],
                       [[], []]],
)


def print_problem(nc, np, na, src, dst, start):
    print("There are {} cities".format(nc))
    print("There are {} packages".format(np))
    print("There are {} airplanes".format(na))
    print()

    assert len(src) == len(dst) == np
    assert len(start) == na

    for i in range(np):
        print("Package P{} starts at city C{} and should be transported to city C{}".format(
            i, src[i], dst[i]))
    print()

    for i in range(na):
        print("Airplane A{} starts at city C{}".format(i, start[i]))
    print()


def print_plan(city_packages, city_airplanes, airplane_packages):
    assert len(city_packages) == len(city_airplanes)
    assert len(city_packages) == len(airplane_packages)

    times = list(range(len(city_packages)))
    nc = len(city_packages[0])
    print("plan:")

    def print_row(row):
        print(' | '.join([''] + ['{:^20}'.format(x) for x in row] + ['']))

    def format_airplane(i, t):
        return 'A{}[{}]'.format(
            i,
            ','.join(['P{}'.format(j) for j in airplane_packages[t][i]])
        )

    print_row(['time'] + ['C{}'.format(i) for i in range(nc)])
    for t in times:
        print_row([t] + [
            ','.join(['P{}'.format(j) for j in city_packages[t][i]] +
            [format_airplane(j, t) for j in city_airplanes[t][i]])
            for i in range(nc)
        ])
    print()


def define_sorts():
    #defining sorts and functions
    C = DeclareSort('C')
    P = DeclareSort('P')
    A = DeclareSort('A')
    at = Function('at', P, C, IntSort(), BoolSort())
    on = Function('on', P, A, IntSort(), BoolSort())
    loc = Function('loc', A, IntSort(), C)
    return C, P, A, at, loc, on

def decalre_consts(nc, np, na, C, P, A):
    #declare constants for cities, airplanes and packages
    cities = [Const(f'C{i}', C) for i in range(nc)]
    packages = [Const(f'P{i}', P) for i in range(np)]
    airplanes = [Const(f'A{i}', A) for i in range(na)]
    return cities, packages, airplanes


def basic_start_end_conditions(packages, cities, airplanes, at, on, loc, src, dst, start, t_finish, s):
    #add conditions for source and destination for all packages
    for i,p in enumerate(packages):
        s.add(at(p, cities[src[i]], 0))
        s.add(at(p, cities[dst[i]], t_finish))
    
    #add conditions for start position of planes
    for i,a in enumerate(airplanes):
        s.add(loc(a, 0) == cities[start[i]])


def add_package_constraints(s, p, t, cities, airplanes, at, on, loc):
    #being on one plane/at one city
    vars_for_at_cities = [at(p, c, t) for c in cities]
    vars_for_on_planes = [on(p, a, t) for a in airplanes]
    s.add(PbEq([(v, 1) for v in vars_for_at_cities+vars_for_on_planes], 1))
    #more package constraints: 
    if t == 0: return
    # if a package is at a city then it either stayed there or was unloaded there.
    for c in cities:
        was_unloaded_from_a_plane = Or(*[And(
            on(p,a,t-1), loc(a,t-1) == c, loc(a,t) == c
        ) for a in airplanes])
        
        s.add(Implies(
            at(p, c, t),
            Or(
                at(p, c, t-1),
                was_unloaded_from_a_plane
            )
        ))
        
    # if a package is on a plane it either stayed there or was loaded there
    for a in airplanes:
        was_loaded_in_a_city = Or(*[And(
            at(p,c,t-1), loc(a,t-1) == c, loc(a,t) == c
        ) for c in cities])
        
        s.add(Implies(
            on(p, a, t),
            Or(
                on(p, a, t-1),
                was_loaded_in_a_city
            )
        ))



def extract_plan_from_model(model, cities, packages, airplanes, t_finish, at, on, loc):
    np = len(packages)
    na = len(airplanes)
    
    city_packages = [
        [
            [i for i in range(np) if is_true(model.eval(at(packages[i], c, t)))] 
            for c in cities
        ] 
        for t in range(t_finish + 1)
    ]
    
    city_airplanes = [
        [
            [i for i in range(na) if is_true(model.eval(loc(airplanes[i], t) == c))] 
            for c in cities
        ] 
        for t in range(t_finish + 1)
    ]
    
    airplane_packages = [
        [
            [i for i in range(np) if is_true(model.eval(on(packages[i], a, t)))] 
            for a in airplanes
        ] 
        for t in range(t_finish + 1)
    ]
    return city_packages, city_airplanes, airplane_packages    


def get_transport_plan(nc, np, na, src, dst, start):
    C, P, A, at, loc, on = define_sorts()
    cities, packages, airplanes = decalre_consts(nc, np, na, C, P, A)
    
    t_finish = 0
    # the maximum number of steps is 4 per package that has an availabl airplane - airplane arrives, airplane loads, aiplane flies, airplane unloads
    t_limit = (np - na + 1) * 4 
    model = None
    
    while model is None and t_finish <= t_limit:
        opt = Optimize() # this is used to minimize airplane moves
        airplane_moves = []
        
        basic_start_end_conditions(packages, cities, airplanes, at, on, loc, src, dst, start, t_finish, opt)
        #add condition for plane to be at one city
        for a in airplanes:
            for t in range(t_finish + 1):
                vars_for_in_cities = [loc(a,t) == c for c in cities]
                opt.add(PbEq([(v, 1) for v in vars_for_in_cities], 1))
                if t > 0:
                    #for optimization:
                    airplane_moves.append(If(loc(a, t) == loc(a, t - 1), 0, 1))# the plane adds a move if it moved
                
        #add conditions for packages 
        for p in packages:
            for t in range(t_finish + 1):
                add_package_constraints(opt, p, t, cities, airplanes, at, on, loc)
            
            
        if t_finish > 0:
            opt.minimize(Sum(airplane_moves)) 
            # we are minimizing within the constraints of t_finish, so the time will still remain optimized
        
        res = opt.check()
        if res == sat:
            print("SAT\n", t_finish)
            model = opt.model()
        elif res == unknown:
            raise Exception('Got unknown from Z3')
        else:
            assert res == unsat
            t_finish += 1

    if model is None:
        print("Time limit reached")
        return None
    else:
        return extract_plan_from_model(model, cities, packages, airplanes, t_finish, at, on, loc)



if __name__ == '__main__':

    print_problem(**example_problem)
    print_plan(**example_solution)
    city_packages, city_airplanes, airplane_packages = get_transport_plan(**example_problem)
    print_plan(city_packages, city_airplanes, airplane_packages)

    #
    # Add more tests here...
    #
