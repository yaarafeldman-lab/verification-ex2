"""
Example of reduction of "job shop" scheduling to SMT (theory of integers).

See slides 16-20 here: http://fmv.jku.at/rerise14/rerise14-smt-slides-1.pdf
"""

from z3 import *

jobs0 = [
    [(1, 2), (2, 1)],
    [(1, 3), (2, 1)],
    [(1, 2), (2, 3)],
]


jobs1 = [
    [(1, 2), (2, 1)],
    [(1, 3), (2, 5), (1, 4)],
    [(1, 7), (2, 6)],
]

def schedule(jobs, time_limit=None):
    n_jobs = len(jobs)

    print("jobs:")
    print(jobs)
    print()

    t = [[Int('t_{}_{}'.format(j, k))
          for k in range(len(jobs[j]))]
         for j in range(n_jobs)]

    print("t = ", t)
    print()

    t_max = max(max(d for m, d in job) for job in jobs)
    if time_limit is None:
        time_limit = sum(sum(d for m, d in job) for job in jobs)
    m = None
    while m is None and t_max <= time_limit:
        print("t_max = ", t_max)
        print()

        s = Solver()

        # job constrains
        for j in range(n_jobs):
            # the first task of job j must start at time >= 0
            s.add(t[j][0] >= 0)
            for k in range(1, len(jobs[j])):
                # the k'th talk of job i must start after the k-1 task finished
                s.add(t[j][k] >= t[j][k-1] + jobs[j][k-1][1])
            # the last task of job j must finish by time t_max
            s.add(t[j][-1] + jobs[j][-1][1] <= t_max)

        # machine constrains
        for j1 in range(n_jobs):
            for j2 in range(j1+1, n_jobs):
                for k1 in range(len(jobs[j1])):
                    for k2 in range(len(jobs[j2])):
                        t1 = t[j1][k1]
                        t2 = t[j2][k2]
                        m1, d1 = jobs[j1][k1]
                        m2, d2 = jobs[j2][k2]
                        if m1 == m2:
                            # two tasks on the same machine must not overlap
                            s.add(Or(t2 >= t1 + d1,
                                     t1 >= t2 + d2))

        print("Solver:")
        print(s)
        print()

        res = s.check()
        if res == sat:
            print("SAT\n")
            m = s.model()
        elif res == unknown:
            raise Exception('Got unknown from Z3')
        else:
            assert res == unsat
            print("UNSAT, increasing t_max\n")
            t_max += 1

    if m is None:
        print("Time limit reached")
        return None
    else:
        # convert model to plan
        plan = [[m[t[j][k]].as_long()
                 for k in range(len(jobs[j]))]
                for j in range(n_jobs)]

        print("t_max = ", t_max)
        print("plan = ", plan)
        print()
        return t_max, plan

def old_print_plan(jobs, plan):
    print("jobs:")
    print(jobs)
    print()

    time_to_task = dict()
    for j in range(len(jobs)):
        for k in range(len(jobs[j])):
            t = plan[j][k]
            if t not in time_to_task:
                time_to_task[t] = []
            time_to_task[t].append((j, k))

    print("plan:")
    t_max = 0
    for t in sorted(time_to_task.keys()):
        for j, k in time_to_task[t]:
            print("    At time {:3}, start task {:3} of job {:3} on machine {:3} with duration {:3} until time {}".format(
                t, k, j, jobs[j][k][0], jobs[j][k][1], t + jobs[j][k][1]
                ))
            t_max = max(t_max, t + jobs[j][k][1])
    print("    Finish at time {}".format(t_max))
    print()


def print_plan(jobs, plan):
    print("jobs:")
    print(jobs)
    print()

    machine_to_time_to_task = dict()
    t_max = 0
    for j in range(len(jobs)):
        for k in range(len(jobs[j])):
            m, d = jobs[j][k]
            t0 = plan[j][k]
            t_max = max(t_max, t0 + d)
            if m not in machine_to_time_to_task:
                machine_to_time_to_task[m] = dict()
            for t in range(t0, t0 + d):
                if t not in machine_to_time_to_task[m]:
                    machine_to_time_to_task[m][t] = []
                machine_to_time_to_task[m][t].append((j, k))

    print("plan:")

    def print_row(row):
        print(' | '.join([''] + ['{:^30}'.format(x) for x in row] + ['']))

    machines = sorted(machine_to_time_to_task.keys())
    print_row(['time'] + ['Machine {}'.format(m) for m in machines])
    for t in range(t_max + 1):
        print_row([t] + [' '.join(str(x) for x in machine_to_time_to_task[m].get(t, [])) for m in machines])
    print()


if __name__ == '__main__':
    print("Example 0\n" + "=" * 80 + "\n")
    t0, p0 = schedule(jobs0)
    print_plan(jobs0, p0)
    print()

    print("Example 1\n" + "=" * 80 + "\n")
    t1, p1 = schedule(jobs1)
    print_plan(jobs1, p1)
    print()
