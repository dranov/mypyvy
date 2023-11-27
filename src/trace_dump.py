from syntax import *
from logic import *

from translator import Z3Translator

import random

# See `pd.py:enumerate_reachable_states`
def generate_traces(s: Solver, how_many: int = 3, max_length: int = 5) -> dict[int, Trace]:
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
        for sort in prog.sorts():
            # TODO: this should be a parameter
            b = 4
            print(f'bounding {sort} to cardinality {b}')
            s.add(s._sort_cardinality_constraint(Z3Translator.sort_to_z3(sort), b))

        # Get a few different instantiations of the initial state
        print('looking for initial states')
        with s.new_frame():
            for init in prog.inits():
                s.add(t1.translate_expr(init.expr))

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