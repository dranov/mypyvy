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

def mk_trace(s: Solver, num_states: int, allow_stutter=False):
    '''Generate a trace with side-conditions on which actions were taken.'''
    # TODO: add cardinality constraints

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
            tids = []
            for ition in prog.transitions():
                call = syntax.TransitionCall(ition.name, None)
                tid_name = get_transition_indicator(str(i), call.target)
                tid = z3.Bool(tid_name)
                s.add(z3.Implies(tid, translate_transition_call(s, lator, i, call)))
                tids.append(tid)

                # Record tid
                tr[i] = tr.get(i, {})
                tr[i][call.target] = tid

            if allow_stutter:
                tid = z3.Bool(get_transition_indicator(str(i), '$stutter'))
                tids.append(tid)
                frame = syntax.And(*DefinitionDecl._frame(prog.scope, mods=()))
                s.add(z3.Implies(tid, lator.translate_expr(New(frame, i))))

            s.add(z3.Or(*tids))

        add_diversity_constraints(s, tr)
        print(f"Generating base-trace of length {num_states}")
        trace = check_unsat([], s, num_states, minimize=False)
        return trace
        
# See `pd.py:enumerate_reachable_states`
def generate_traces(s: Solver, how_many: int = 3, base_length: int = 5, max_length: int = 25) -> dict[int, list[(str, State)]]:
    assert max_length >= base_length, f"max_length ({max_length}) must be >= base_length ({base_length})"

    prog = syntax.the_program
    
    # TODO: use traces declared using `sat trace` as base traces
    # Create a trace that is reasonably diverse (expensive SMT query)
    # then extend it cheaply at random (with cheap queries)
    base_trace = mk_trace(s, base_length, allow_stutter=True)

    if base_trace is None:
        print("No base trace satisfying conditions found! Aborting.")
    print(f"Found base trace of length {base_length}: {base_trace.transitions}")

    # Last state in base_trace has idx = base_length - 2
    # lator = s.get_translator(max_length)
    t1 = s.get_translator(1) # translator for one-state formulas
    t2 = s.get_translator(2) # translator for two-state formulas

    num_traces = 0
    # Each entry is a (transition_name, post_state) pair
    # for init, transition_name = ''
    traces: dict[int, list[(str, State)]] = {}

    def trace_to_state_list(t: Trace) -> list[(str, State)]:
        assert len(t.transitions) == t.num_states - 1
        x = []
        for sid in range(t.num_states):
            tname = '' if sid == 0 else t.transitions[sid - 1]
            x.append((tname, t.as_state(sid)))
        return x

    for t_id in range(how_many):
        print(f'\nextending trace {t_id}')
        traces[t_id] = trace_to_state_list(base_trace)
        
        for i in range(base_length - 1, max_length - 1):
            # Randomly pick a satisfying transition
            itions = list(prog.transitions())
            random.shuffle(itions)
            found_transition = False
            for ition in itions:
                if found_transition:
                    break

                with s.new_frame():
                        s.add(t2.translate_expr(ition.as_twostate_formula(prog.scope)))
                        res = s.check()
                        if res == z3.sat:
                            m = Z3Translator.model_to_trace(s.model(minimize=False), 2)
                            print(f'... found extension of trace {t_id} to length {i + 1} via {ition.name}')
                            post = m.as_state(1)
                            traces[t_id].append((ition.name, post))
                            found_transition = True
                        elif res == z3.unsat:
                            # print(f'... could not extend trace {t_id} to length {i + 1} via {ition.name}')
                            pass
                        elif res == z3.unknown:
                            print(f'solver returned unknown for {ition.name}')

    # import pdb; pdb.set_trace()
    return traces