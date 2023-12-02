# The purpose of this file is to generate "interesting" and "diverse" traces
# for a given specification, and dump them in a CSV format understood by DuoAI.

from syntax import *
from logic import *

from translator import Z3Translator
from trace import translate_transition_call

import random


def add_diversity_constraints(s: Solver, tr: dict[int, dict[str, z3.Bool]]):
    prog = syntax.the_program
    num_tr = len(tr)

    # (1) the same transition does not happen three times in a row
    if num_tr >= 3:
        print("Adding constraint: not-three-times-in-a-row")
        for i in range(num_tr - 2):
            for n in tr[i].keys():
                s.add(z3.Implies(z3.And(tr[i][n], tr[i + 1][n]), z3.Not(tr[i + 2][n])))

    # (2) every transition happens at least once
    if num_tr >= len(list(prog.transitions())):
        print("Adding constraint: every-transition-at-least-once")
        for ition in prog.transitions():
            occ = [tr[i][ition.name] for i in tr.keys()]
            s.add(z3.Or(*occ))

    return

def mk_trace(s: Solver, num_states: int = 5):
    '''Generate a trace with side-conditions on which actions were taken.'''

    prog = syntax.the_program
    lator = s.get_translator(num_states)

    # Mapping from state ID to all transition indicators for that state
    # Used to construct diversity side-conditions.
    tr: dict[int, list[(str, z3.Bool)]] = {}

    with s.new_frame():
        if num_states > 0:
            for init in prog.inits():
                s.add(lator.translate_expr(init.expr))

        for i in range(0, num_states - 1):
            l = []
            for ition in prog.transitions():
                call = syntax.TransitionCall(ition.name, None)
                tid_name = get_transition_indicator(str(i), call.target)
                tid = z3.Bool(tid_name)
                s.add(z3.Implies(tid, translate_transition_call(s, lator, i, call)))
                l.append(tid)

                # Record tid
                tr[i] = tr.get(i, {})
                tr[i][call.target] = tid

            s.add(z3.Or(*l))

        add_diversity_constraints(s, tr)
        trace = check_unsat([], s, num_states)
        print(trace)
        # import pdb; pdb.set_trace()

        
# See `pd.py:enumerate_reachable_states`
def generate_traces(s: Solver, how_many: int = 3, max_length: int = 5) -> dict[int, Trace]:

    mk_trace(s, 5)
    return {}

    # TODO: take as input sort cardinality constraints
    prog = syntax.the_program
    t1 = s.get_translator(1) # translator for one-state formulas
    t2 = s.get_translator(2) # translator for two-state formulas

    def block_state(t: Z3Translator, m: Trace) -> None:
        # See comment in `pd:py:enumerate_reachable_states`
        s.add(t.translate_expr(New(Not(m.as_onestate_formula(0)), t.num_states - 1)))

    num_traces = 0
    traces: dict[int, list[State]] = {}

    def create_new_trace(init: Trace):
        nonlocal num_traces
        trace_id = num_traces
        num_traces += 1
        traces[trace_id] = [init.as_state(0)]
    
    with s.new_frame():
        # for sort in prog.sorts():
        #     # TODO: this should be a parameter
        #     b = 4
        #     print(f'bounding {sort} to cardinality {b}')
        #     s.add(s._sort_cardinality_constraint(Z3Translator.sort_to_z3(sort), b))

        # Get a few different instantiations of the initial state
        print('looking for initial states')
        with s.new_frame():
            for init in prog.inits():
                s.add(t1.translate_expr(init.expr))

            # TODO: we want "interesting" initial states.
            # It seems for the Token contract, some/many initial
            # states lead to certain transitions only being able
            # to panic. We want to avoid these.

            while num_traces < how_many:
                res = s.check()
                if res == z3.sat:
                    m = Z3Translator.model_to_trace(s.model(minimize=False), 1)
                    create_new_trace(m)
                    block_state(t1, m)
                    print(f'... found initial state {num_traces}')
                elif res == z3.unsat:
                    print('no more initial states')
                    break
                else:
                    print("solver returned unknown")
                    break

        print(f'found {num_traces} initial states!')

    # Extend the traces up to the maximum length
    # TODO: should this be under the cardinality constraint?
    for t_id in range(num_traces):
        print(f'\nextending trace {t_id}')
        for i in range(1, max_length):
            assert i == len(traces[t_id])
            last_state = traces[t_id][-1]
            with s.new_frame():
                pre = last_state.as_onestate_formula()
                s.add(t2.translate_expr(pre))
                # I don't think we want this; we want some diversity
                # rather than allow the solver to pick the same transition
                # over and over again, which this can lead to
                # assert_any_transition(s, t2, 0, False)

                # Randomly pick a satisfying transition
                itions = list(prog.transitions())
                random.shuffle(itions)
                # print(list(map(lambda x: x.name, itions)))
                found_transition = False

                for ition in itions:
                    if found_transition:
                        break
                    with s.new_frame():
                        s.add(t2.translate_expr(ition.as_twostate_formula(prog.scope)))
                        # tid = z3.Bool(get_transition_indicator(str(0), ition.name))
                        # s.add(z3.Implies(tid, t2.translate_expr(New(ition.as_twostate_formula(prog.scope), 0))))
                        res = s.check()
                        if res == z3.sat:
                            m = Z3Translator.model_to_trace(s.model(minimize=False), 2)
                            print(f'... found extension of trace {t_id} to length {i + 1} via {ition.name}')
                            post = m.as_state(1)
                            # import pdb; pdb.set_trace()
                            traces[t_id].append(post)
                            found_transition = True
                        elif res == z3.unsat:
                            pass
                            # print(f'... could not extend trace {t_id} to length {i + 1} via {ition.name}')
                        elif res == z3.unknown:
                            print(f'solver returned unknown for {ition.name}')

                if not found_transition:
                    print(f'... could not extend trace {t_id} to length {i + 1}')
                    break                        

    import pdb; pdb.set_trace()