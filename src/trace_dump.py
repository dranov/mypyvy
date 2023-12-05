# The purpose of this file is to generate "interesting" and "diverse" traces
# for a given specification, and dump them in a CSV format understood by DuoAI.

from syntax import *
from logic import *

from translator import Z3Translator
from trace import translate_transition_call

import copy
import pandas as pd
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

def mk_trace(s: Solver, num_states: int, sort_sizes: Optional[list[int]] = None, allow_stutter=False):
    '''Generate a trace with side-conditions on which actions were taken.'''
    # TODO: add cardinality constraints

    prog = syntax.the_program
    lator = s.get_translator(num_states)

    # Mapping from state ID to all transition indicators for that state
    # Used to construct diversity side-conditions.
    tr: dict[int, list[(str, z3.Bool)]] = {}

    with s.new_frame():
        # Bound sort sizes
        if sort_sizes is not None:
            for (i, sort) in enumerate(prog.sorts()):
                b = sort_sizes[i]
                print(f'bounding {sort} to cardinality {b}')
                s.add(s._sort_strict_cardinality_constraint(Z3Translator.sort_to_z3(sort), b))

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

        # add_diversity_constraints(s, tr)
        print(f"Generating base-trace of length {num_states}")
        trace = check_unsat([], s, num_states, minimize=False, verbose=False)
        return trace
        
# See `pd.py:enumerate_reachable_states`
def generate_trace(s: Solver, max_length: int = 25, sort_sizes: Optional[list[int]] = None, sort_elems: Optional[dict[tuple[int], list[str]]] = None, pred_columns: Optional[list[str]] = None, filename="trace-dump.csv", base_length: int = 5) -> dict[int, list[(str, State)]]:
    assert max_length >= base_length, f"max_length ({max_length}) must be >= base_length ({base_length})"

    prog = syntax.the_program
    
    # TODO: use traces declared using `sat trace` as base traces
    # Create a trace that is reasonably diverse (expensive SMT query)
    # then extend it cheaply at random (with cheap queries)
    base_trace = mk_trace(s, base_length, sort_sizes, allow_stutter=False)

    if base_trace is None:
        print("No base trace satisfying conditions found! Aborting.")
        # FIXME: generate CSV with just the header when no traces are found
    # print(f"Found base trace of length {base_length}: {base_trace.transitions}")

    # Last state in base_trace has idx = base_length - 2
    # lator = s.get_translator(max_length)
    t1 = s.get_translator(1) # translator for one-state formulas
    t2 = s.get_translator(2) # translator for two-state formulas

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

    t_id = 0
    print(f'\nTrace {t_id}')
    traces[t_id] = trace_to_state_list(base_trace)
    for (i, (tname, _st)) in enumerate(traces[t_id][1:]):
        print(f'... transition {i}: {tname}')
    
    for i in range(base_length - 1, max_length - 1):
        assert len(traces[t_id]) == i + 1, f"trace {t_id} has length {len(traces[t_id])} but should have length {i + 1}"
        with s.new_frame():
            # Assert the current state
            (_last_tr, last_state) = traces[t_id][-1]
            s.add(t1.translate_expr(last_state.as_onestate_formula()))

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
                        print(f'... transition {i + 1}: {ition.name}')
                        post = m.as_state(1)
                        traces[t_id].append((ition.name, post))
                        found_transition = True
                    elif res == z3.unsat:
                        # print(f'... could not extend trace {t_id} to length {i + 1} via {ition.name}')
                        pass
                    elif res == z3.unknown:
                        print(f'solver returned unknown for {ition.name}')

            if not found_transition:
                print(f'... could not extend trace {t_id} to length {i + 1}')
                break

    # dump_trace_txt(t_id, traces[t_id], f"trace_{t_id}.txt")
    dump_trace_csv(t_id, traces[t_id], filename, sort_elems, pred_columns)

    return traces

def dump_trace_txt(id: int, tr: list[(str, State)], filename: str):
    print(f"Dumping trace {id} to {filename}...")
    with open(filename, 'w') as f:
        for (i, (tname, state)) in enumerate(tr):
            if i == 0:
                f.write(f'state {i}:\n\n{state}\n\n')
            else:
                f.write(f'transition {tname}\n\nstate {i}:\n\n{state}\n\n')

def dump_trace_csv(i: int, tr: list[(str, State)], filename: str, sort_elems: Optional[dict[tuple[int], list[str]]] = None, pred_columns: Optional[list[str]] = None):
    print(f"Dumping trace to {filename}...")
    def elem_to_univ_name(elem: str) -> str:
        # FIXME: make this work with more than 10 elements
        return str.upper(elem[0]) + str(int(elem[-1]) + 1)
    

    def parse_state(st: State) -> dict[str, bool]:
        nonlocal sort_elems, pred_columns
        d = {}  # dictionary to dump everything into

        # mapping from mypyvy sort element name (e.g. 'epoch0') to
        # DuoAI sort element name (e.g. 'E1')
        to_duo = {}
        to_mypyvy = {}

        # Parse sorts
        sorts = {}
        for (sort, elems) in st.univs.items():
            if sort_elems is None:
                sorts[sort.name] = list(map(elem_to_univ_name, elems))
            else:
                assert sort.name in sort_elems, f"sort {sort.name} not found in sort_elems"
                assert len(elems) == len(sort_elems[sort.name]), f"sort {sort.name} has {len(elems)} elements but sort_elems has {len(sort_elems[sort.name])} elements"
                sorts[sort.name] = sort_elems[sort.name]
                for (i, elem) in enumerate(elems):
                    to_duo[elem] = sort_elems[sort.name][i]
                    to_mypyvy[sort_elems[sort.name][i]] = elem

        def eval_duo_expr(dexpr: str, in_st:State):
            e = parser.parse_expr(dexpr)
            subst = { Id(k):Id(v) for (k, v) in to_mypyvy.items() }
            en = syntax.subst_vars_simple(e, subst)
            interp = in_st.eval(en)
            # Fix for booleans
            if isinstance(interp, dict) and () in interp:
                interp = True if interp[()] else False
            return interp

        # Dump predicates (DuoAI)
        if pred_columns is not None:
            # HACK: add constants for all sort elements to the state
            # so we can evaluate the expression. We need to artificially
            # create some inner state to make this work.
            new_constants = {}
            for (sort_decl, elems) in st.univs.items():
                for elem in elems:
                    _sort = UninterpretedSort(sort_decl.name)
                    _sort.decl = sort_decl
                    cnst = ConstantDecl(elem, _sort, mutable=False)
                    new_constants[cnst] = elem
            st.trace.immut_const_interps.update(new_constants)
            # add our fake constants to the scope
            orig_scope = copy.deepcopy(syntax.the_program.scope)
            for cnst in new_constants.keys():
                syntax.the_program.scope.add_constant(cnst)

            for pred in pred_columns:
                d[pred] = eval_duo_expr(pred, st)

            syntax.the_program.scope = orig_scope # restore original scope
        # Dump predicate (no DuoAI)
        else:
            # Dump constants/individuals
            for (const, interp) in st.const_interps.items():
                # Special case for booleans
                if isinstance(const.sort, syntax._BoolSort):
                    d[const.name] = True if interp[()] else False
                else:
                    sort = const.sort.name
                    assert sort in sorts, f"sort {sort} not found in initial state"
                    interp = elem_to_univ_name(interp)
                    for elem in sorts[sort]:
                        name = f"{const.name}={elem}"
                        d[name] = True if elem == interp else False

            # Dump relations
            for (rel, interp) in st.rel_interps.items():
                if rel.arity == 0:
                    d[rel.name] = True if interp else False
                else:
                    for (args, val) in interp.items():
                        name = f"{rel.name}({','.join(map(elem_to_univ_name, args))})"
                        d[name] = True if val else False

            # TODO: handle functions; it's a bit unclear what DuoAI's
            # translate.py does for them.

        return (d, sorts)

    xs = [parse_state(st) for (_tname, st) in tr]
    # Sanity check: all sorts are the same
    assert all(x[1] == xs[0][1] for x in xs), "sorts must be the same across all states in a trace"
    xs = [x[0] for x in xs]

    df = pd.DataFrame(xs)
    df.replace({False: 0, True: 1}, inplace=True)
    df.to_csv(filename, index=False)

def dump_traces(traces: dict[int, list[(str, State)]], base_filename: str):
    for i in traces.keys():
        dump_trace_txt(i, traces[i], f"{base_filename}_{i}.txt")
