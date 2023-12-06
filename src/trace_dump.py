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

GIVE_UP_AFTER_N_UNEVENTFUL_SIMULATIONS = sys.maxsize

GIVE_UP_AFTER_N_CONSECUTIVE_DUPS = 100

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

def expand_explicit_state(s: Solver, max_states: int = 25, sort_sizes: Optional[list[int]] = None, sort_elems: Optional[dict[tuple[int], list[str]]] = None, pred_columns: Optional[list[str]] = None, filename="trace-dump.csv"):
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

    def assert_transition(s: Solver, ition: DefinitionDecl):
        call = syntax.TransitionCall(ition.name, None)
        tid_name = get_transition_indicator(str(i), call.target)
        tid = z3.Bool(tid_name)
        tr = translate_transition_call(s, t2, 0, call)
        s.add(z3.Implies(tid, tr))
        s.add(tid)

    def unexplored_transitions() -> set[str]:
        return all_transitions.difference(transitions_successfully_taken)

    with s.new_frame():
        # Bound sort sizes
        if sort_sizes is not None:
            for (i, sort) in enumerate(prog.sorts()):
                b = sort_sizes[i]
                print(f'bounding {sort} to cardinality {b}')
                s.add(s._sort_strict_cardinality_constraint(Z3Translator.sort_to_z3(sort), b))

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
                            assert_transition(s, ition)
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
                                assert_transition(s, ition)
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

        exhaustive_breadth_first()
        random_action_expansion()

    fake_trace = [(f"state_{i}", st) for (i, st) in reached_states.items()]
    dump_trace_csv(fake_trace, filename, sort_elems, pred_columns)


# See `pd.py:enumerate_reachable_states`
def generate_reachable_states(s: Solver, max_states: int = 25, sort_sizes: Optional[list[int]] = None, sort_elems: Optional[dict[tuple[int], list[str]]] = None, pred_columns: Optional[list[str]] = None, filename="trace-dump.csv"):
    '''Generates list of reachable states, not necesarily valid traces.'''
    prog = syntax.the_program
    t1 = s.get_translator(1) # translator for one-state formulas
    t2 = s.get_translator(2) # translator for two-state formulas

    blocked_states = {}
    reached_states = {}
    # reachable states at a certain depth
    reachable_states: dict[int, list[State]] = {0: []}
    num_states = 0
    num_duplicates = 0
    # These are pre-depths
    available_depths = set([-1])

    def block_post_state(s: Solver, m: State):
        state_id = parse_state_to_str(m, sort_elems, pred_columns)
        assert state_id not in blocked_states, f"state {state_id} already blocked!"
        blocked_states[state_id] = m

        # FIXME: why is blocking so unbelievably slow?
        pyv_fmla = New(Not(m.as_onestate_formula()))
        z3_fmla = t2.translate_expr(pyv_fmla)
        s.add(z3_fmla)

    def assert_state_at_depth(s: Solver, d: int):
        if d <= 0:
            for init in prog.inits():
                s.add(t1.translate_expr(init.expr))
        else:
            # Pick any one of the reachable states at depth d - 1
            # pres = [t1.translate_expr(m.as_onestate_formula()) for m in reachable_states[d - 1]]
            # s.add(z3.Or(*pres))
            rs = random.choice(reachable_states[d - 1])
            s.add(t1.translate_expr(rs.as_onestate_formula()))

    def assert_some_transition(s: Solver):
        # Assert any transition from that state
        tids = []
        for ition in prog.transitions():
            call = syntax.TransitionCall(ition.name, None)
            tid_name = get_transition_indicator(str(i), call.target)
            tid = z3.Bool(tid_name)
            tr = translate_transition_call(s, t2, 0, call)
            # tr = t2.translate_expr(ition.as_twostate_formula(syntax.the_program.scope))
            s.add(z3.Implies(tid, tr))
            tids.append(tid)
        s.add(z3.Or(*tids))

    def get_and_record_post_state(s: Solver, d: int) -> Optional[State]:
        nonlocal reachable_states, num_states, available_depths
        num_states_in_model = 1 if d == 0 else 2

        res = s.check()
        if res == z3.sat: 
            m = Z3Translator.model_to_trace(s.model(minimize=False), num_states_in_model)
            post = m.as_state(num_states_in_model - 1)
            # print(f'... found state {hash(post)} at depth {d}')
            state_id = parse_state_to_str(post, sort_elems, pred_columns)
            if state_id in reached_states:
                return None
            else:
                reachable_states[d] = reachable_states.get(d, [])
                reachable_states[d].append(post)
                reached_states[state_id] = post
                num_states += 1
                available_depths.add(d)
                return post
        elif res == z3.unsat:
            return None
        elif res == z3.unknown:
            assert False, "should not be unknown"
           
    with s.new_frame():
        # Bound sort sizes
        if sort_sizes is not None:
            for (i, sort) in enumerate(prog.sorts()):
                b = sort_sizes[i]
                print(f'bounding {sort} to cardinality {b}')
                s.add(s._sort_strict_cardinality_constraint(Z3Translator.sort_to_z3(sort), b))

        num_dups_in_a_row = 0
        while (num_states + num_duplicates < max_states) and (num_dups_in_a_row < GIVE_UP_AFTER_N_CONSECUTIVE_DUPS):
            # Pick an available pre-depth
            d = random.choice(list(available_depths))
            # d = min(available_depths)

            diag = [len(reachable_states[k]) for k in sorted(list(reachable_states.keys()))]
            print(f'{num_states}/{max_states}: diag {diag} | {num_duplicates} dups | chosen depth {d}')
            # print(f"blocked states: {blocked_fingerprints}")
            # import pdb; pdb.set_trace()

            s.push()
            # print(f'... asserting state at depth {d}')
            assert_state_at_depth(s, d)
            assert_some_transition(s)
            st = get_and_record_post_state(s, d + 1)
            s.pop()
            if st is not None:
                # block_post_state(s, st)
                num_dups_in_a_row = 0
            else:
                # print(f'found duplicate state extending from depth {d}; nothing left to explore there')
                # available_depths.remove(d)
                num_duplicates += 1
                num_dups_in_a_row += 1

    print(f"Found {len(reached_states)} unique reachable states (hit {num_duplicates} duplicates)")
    fake_trace = [(f"state_{i}", st) for (i, st) in reached_states.items()]
    dump_trace_csv(fake_trace, filename, sort_elems, pred_columns)

def generate_trace(s: Solver, max_length: int = 25, sort_sizes: Optional[list[int]] = None, sort_elems: Optional[dict[tuple[int], list[str]]] = None, pred_columns: Optional[list[str]] = None, filename="trace-dump.csv", base_length: int = 5) -> dict[int, list[(str, State)]]:
    '''Generates valid traces, i.e. sequences of states.'''
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
                    # Block previous state: we don't want no-ops
                    # s.add(t2.translate_expr(New(Not(last_state.as_onestate_formula()))))

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
    dump_trace_csv(traces[t_id], filename, sort_elems, pred_columns)

    return traces

def dump_trace_txt(id: int, tr: list[(str, State)], filename: str):
    print(f"Dumping trace {id} to {filename}...")
    with open(filename, 'w') as f:
        for (i, (tname, state)) in enumerate(tr):
            if i == 0:
                f.write(f'state {i}:\n\n{state}\n\n')
            else:
                f.write(f'transition {tname}\n\nstate {i}:\n\n{state}\n\n')

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

def dump_traces(traces: dict[int, list[(str, State)]], base_filename: str):
    for i in traces.keys():
        dump_trace_txt(i, traces[i], f"{base_filename}_{i}.txt")

def parse_state_to_str(st: State, sort_elems: Optional[dict[tuple[int], list[str]]] = None, pred_columns: Optional[list[str]] = None) -> str:
    (d, _sorts) = parse_state(st, sort_elems, pred_columns)
    df = pd.DataFrame([d])
    df.replace({False: 0, True: 1}, inplace=True)
    return str(df.loc[0].values.tolist())

def parse_state(st: State, sort_elems: Optional[dict[tuple[int], list[str]]] = None, pred_columns: Optional[list[str]] = None) -> dict[str, bool]:
    def elem_to_univ_name(elem: str) -> str:
        # FIXME: make this work with more than 10 elements
        return str.upper(elem[0]) + str(int(elem[-1]) + 1)

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
        if isinstance(interp, str):
            assert interp in ['true', 'false']
            interp = False if interp == 'false' else True
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
