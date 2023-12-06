# The purpose of this file is to generate "interesting" and "diverse" traces
# for a given specification, and dump them in a CSV format understood by DuoAI.

from syntax import *
from logic import *

from translator import Z3Translator
from trace import translate_transition_call

import collections
import copy
import numpy as np
import pandas as pd
import random
import sys

rng = np.random.default_rng(0)
RAND_ACTION_MAX_ITER = 50

GIVE_UP_AFTER_N_UNEVENTFUL_SIMULATIONS = 5

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

def expand_explicit_state(s: Solver, max_states: int = 25, pyv_sort_elems: Optional[dict[str, list[str]]] = None, duo_sort_elems: Optional[dict[tuple[int], list[str]]] = None, pred_columns: Optional[list[str]] = None, filename="trace-dump.csv"):
    prog = syntax.the_program
    t1 = s.get_translator(1) # translator for one-state formulas
    t2 = s.get_translator(2) # translator for two-state formulas

    reached_states = {}
    # StateID -> (depth, State)
    to_expand: dict[str, (int, State)] = collections.OrderedDict()
    transitions_successfully_taken = set()
    all_transitions = set([ition.name for ition in prog.transitions()])

    def state_id(st: State) -> str:
        # return parse_state_to_str(st, sort_elems, pred_columns)
        return st._unique_id()

    def block(s: Solver, st: State):
        pyv_fmla = Not(st.as_onestate_formula())
        z3_fmla = t2.translate_expr(pyv_fmla)
        s.add(z3_fmla)

    def get_post_state(s: Solver, one_state=False) -> Optional[State]:
        num_states_in_model = 1 if one_state else 2
        res = s.check()
        if res == z3.sat:
            m = Z3Translator.model_to_trace(s.model(minimize=False), num_states_in_model)
            post = m.as_state(num_states_in_model - 1)
            return post
        elif res == z3.unsat:
            return None
        elif res == z3.unknown:
            assert False, "should not be unknown"

    def assert_state(s: Solver, st: State):
        s.add(t1.translate_expr(st.as_onestate_formula()))

    def assert_transition_any_args(s: Solver, ition: DefinitionDecl):
        call = syntax.TransitionCall(ition.name, None)
        tid_name = get_transition_indicator('0', call.target)
        tid = z3.Bool(tid_name)
        tr = translate_transition_call(s, t2, 0, call)
        s.add(z3.Implies(tid, tr))
        s.add(tid)

    def assert_transition_random_args(s: Solver, ition: DefinitionDecl):
        def random_var(sort_decl):
            return rng.choice(pyv_sort_elems[sort_decl.name])
        args = []
        for b in ition.binder.vs:
            args.append(Id(random_var(b.sort)))
        # print(f"{ition.name}({','.join(map(str, args))})")
        call = syntax.TransitionCall(ition.name, args)
        tid_name = get_transition_indicator('0', call.target)
        tid = z3.Bool(tid_name)
        tr = translate_transition_call(s, t2, 0, call)
        s.add(z3.Implies(tid, tr))
        s.add(tid)

    def unexplored_transitions() -> set[str]:
        return all_transitions.difference(transitions_successfully_taken)

    with s.new_frame():
        # Enumerate initial states
        with s.new_frame():
            for init in prog.inits():
                s.add(t1.translate_expr(init.expr))

            while True:
                st = get_post_state(s, one_state=True)
                if st is None:
                    break
                sid = state_id(st)
                reached_states[sid] = st
                to_expand[sid] = (0, st)
                block(s, st)

        print(f"Found {len(reached_states)} unique initial states!")
        initial_states = copy.deepcopy(reached_states)

        def exhaustive_breadth_first(max_states=max_states):
            '''Perform a breadth-first search of the state space. Stop
            expanding at depth two more than when all transitions are explored,
            AND `max_states` states are reached.'''
            stop_depth = sys.maxsize
            last_depth = 0
            # Expansion loop
            while True:
                if len(to_expand) == 0:
                    print("No more states to expand!")
                    break

                if last_depth >= stop_depth:
                    print(f"Reached maximum depth {stop_depth}!")
                    break

                if len(reached_states) >= max_states:
                    print(f"Reached maximum number of states {max_states}!")
                    break
                
                if len(unexplored_transitions()) == 0 and stop_depth == sys.maxsize:
                    stop_depth = last_depth + 2
            
                # FIFO
                (key_choice, (depth, rand_state)) = to_expand.popitem(last=False)
                last_depth = max(last_depth, depth)
                stop_depth_str = 'INF' if stop_depth == sys.maxsize else str(stop_depth) 
                print(f"Reached {len(reached_states)} states; popped at depth {depth}/{stop_depth_str} (unexplored transitions: {unexplored_transitions()}); expanding...")
                with s.new_frame():
                    assert_state(s, rand_state)
                    # Expand with every transition
                    for ition in prog.transitions():
                        with s.new_frame():
                            # FIXME: we need to try EVERY possible argument
                            assert_transition_any_args(s, ition)
                            # FIXME: ... and get all possible post states for each argument
                            # (by blocking previously seen post-states)
                            st = get_post_state(s)
                            if st is not None:
                                sid = state_id(st)
                                # print(f"{hash(tuple(key_choice))} -> {hash(tuple(sid))} (via {ition.name})")
                                transitions_successfully_taken.add(ition.name)
                                if sid not in reached_states:
                                    reached_states[sid] = st
                                    to_expand[sid] = (depth + 1, st)
        
        def random_action_expansion(max_simulation_rounds=max_states):
            '''Repeatedly expand a state with a random enabled transition
            until no action is enabled anymore.'''
            simulation_round = 0
            (num_eventful_simulations, last_len_reached) = (0, len(reached_states))
            while simulation_round < max_simulation_rounds:
                with s.new_frame():
                    # Random initial state
                    key_choice = random.choice(list(initial_states.keys()))
                    st = initial_states[key_choice]
                    assert_state(s, st)
                    for curr_iter in range(RAND_ACTION_MAX_ITER):
                        print(f"Round {simulation_round} | Iteration {curr_iter} | Reached {len(reached_states)} unique states; expanding...")
                        # Expand with a random enabled transition
                        enabled_transition = False
                        transitions = list(prog.transitions())
                        rng.shuffle(transitions)
                        for ition in transitions:
                            with s.new_frame():
                                # assert_transition_any_args(s, ition)
                                assert_transition_random_args(s, ition)
                                post_st = get_post_state(s)
                                if post_st is not None:
                                    enabled_transition = True
                                    pre_sid = state_id(st)
                                    post_sid = state_id(post_st)
                                    # print(f"{hash(tuple(pre_sid))} -> {hash(tuple(post_sid))} (via {ition.name})")
                                    reached_states[post_sid] = post_st
                                    st = post_st # Move to next iteration
                                    break
                        if not enabled_transition:
                            print(f"Advancing to next simulation round ({simulation_round})...")
                            break
                    if len(reached_states) == last_len_reached:
                        num_eventful_simulations += 1
                        if num_eventful_simulations >= GIVE_UP_AFTER_N_UNEVENTFUL_SIMULATIONS:
                            print(f"Reached {len(reached_states)} unique states; giving up after {num_eventful_simulations} uneventful simulations")
                            break
                    else:
                        num_eventful_simulations = 0
                        last_len_reached = len(reached_states)
                simulation_round += 1

        # exhaustive_breadth_first()
        random_action_expansion()

    fake_trace = [(f"state_{i}", st) for (i, st) in reached_states.items()]
    dump_trace_csv(fake_trace, filename, duo_sort_elems, pred_columns)


def dump_trace_csv(tr: list[(str, State)], filename: str, sort_elems: Optional[dict[tuple[int], list[str]]] = None, pred_columns: Optional[list[str]] = None):
    print(f"Dumping trace to {filename}...")
    xs = [parse_state(st, sort_elems, pred_columns) for (_tname, st) in tr]
    # Sanity check: all sorts are the same
    assert all(x[1] == xs[0][1] for x in xs), "sorts must be the same across all states in a trace"
    xs = [x[0] for x in xs]

    df = pd.DataFrame(xs)
    df.replace({False: 0, True: 1}, inplace=True)
    df.sort_values(df.columns.tolist(), inplace=True)
    df.drop_duplicates(inplace=True)
    df.to_csv(filename, index=False)

def parse_state_to_str(st: State, sort_elems: Optional[dict[tuple[int], list[str]]] = None, pred_columns: Optional[list[str]] = None) -> str:
    (d, _sorts) = parse_state(st, sort_elems, pred_columns)
    df = pd.DataFrame([d])
    df.replace({False: 0, True: 1}, inplace=True)
    return str(df.loc[0].values.tolist())

def parse_state(st: State, sort_elems: Optional[dict[tuple[int], list[str]]] = None, pred_columns: Optional[list[str]] = None) -> dict[str, bool]:
    def elem_to_univ_name(elem: str) -> str:
        # FIXME: make this work with more than 10 elements
        # return str.upper(elem[0]) + str(int(elem[-1]) + 1)
        return elem

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
                to_mypyvy[sort_elems[sort.name][i]] = f"__{elem}"

    def eval_duo_expr(dexpr: str, in_st:State):
        e = parser.parse_expr(dexpr)
        subst = { Id(k):Id(v) for (k, v) in to_mypyvy.items() }
        en = syntax.subst(syntax.the_program.scope, e, subst)
        return eval_pyv_expr(str(en), in_st)
    
    def eval_pyv_expr(pexpr: str, in_st:State):
        e = parse_and_typecheck_expr(pexpr, 1, close_free_vars=True)
        interp = in_st.eval(e)
        # Fix for booleans
        if isinstance(interp, dict) and () in interp:
            interp = True if interp[()] else False
        if isinstance(interp, str):
            assert interp in ['true', 'false']
            interp = False if interp == 'false' else True
        return interp

    # Dump predicates (DuoAI)
    if pred_columns is not None:
        for pred in pred_columns:
            d[pred] = eval_duo_expr(pred, st)
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
