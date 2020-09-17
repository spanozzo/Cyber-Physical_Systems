import pynusmv
import sys

def isEmpty(model, x):
    """
    Return True if the BDD is empty
    x : BDD
    model : finite-state machine of the model
    """
    if model.count_states(x) == 0:
        return True
    return False 

def spec_to_bdd(model, spec):
    """
    Return the set of states of `model` satisfying `spec`, as a BDD.
    """
    bddspec = pynusmv.mc.eval_ctl_spec(model, spec)
    return bddspec

def reachable_states(model):
    """
    Returns the region representing all reachable states, given the initial states of the model
    model : finite-state machine of the model
    """
    init = model.init 
    reach = init 
    new = init 
    while not(isEmpty(model, new)): 
        new = model.post(new).diff(reach)
        reach = new.union(reach)
    return reach
    
def check_explain_eventually_old(spec):
    ltlspec = pynusmv.prop.f(spec)
    print("eventually ltlspec: ", ltlspec)
    model = pynusmv.glob.prop_database().master.bddFsm
    bddspec = spec_to_bdd(model, spec)
    trace = []
    res = True
    state = model.init
    reachable = reachable_states(model)
    not_property = reachable.diff(bddspec)    
    not_property_set = model.pick_all_states(not_property)
    for bad_state in not_property_set:
        stop = False
        if(res):
            trace.clear()
            # find all the states reachable from the "bad" state (i.e. state that doesn't satisfy the formula)
            state = bad_state
            reach = pynusmv.dd.BDD.false()
            while not(isEmpty(model, state.diff(reach))) and not stop:
                reach = reach.union(state)
                state = model.post(state)
                if(isEmpty(model, state.diff(bddspec))):
                    stop = True
            state = bad_state
            while not(isEmpty(model, state.diff(reach))) and not stop:       
                reach = reach.union(state)
                state = model.pre(state)
                if(isEmpty(model, state.diff(bddspec))):
                    stop = True
            # reach contains all reachable states from the "bad" state
            # bad_reach contains all states reachable from the "bad" state that do not satisfy the formula
            bad_reach = reach.diff(bddspec)
            initial_state = bad_reach.intersection(model.init)  
            if not(isEmpty(model, initial_state)):
                res = False
                initial_state = model.pick_one_state(initial_state)
                state = initial_state
                trace.append(initial_state.get_str_values())
                reached = pynusmv.dd.BDD.false()
                while not(isEmpty(model, state.diff(reached))):
                    reached = reached.union(state)
                    post = model.post(state)
                    post = post.diff(bddspec)
                    inp = model.get_inputs_between_states(state, post)
                    if not(isEmpty(model, inp)):
                        inp_i = model.pick_one_inputs(inp)
                        state = model.post(state, inp_i)
                        state_s = model.pick_one_state(state)
                        trace.append(inp_i.get_str_values())
                        trace.append(state_s.get_str_values())
                    else: 
                        res = True
                        trace.clear()
    return res, trace

def check_explain_eventually(spec):
    ltlspec = pynusmv.prop.f(spec)
    print("eventually ltlspec: ", ltlspec)
    model = pynusmv.glob.prop_database().master.bddFsm
    bddspec = spec_to_bdd(model, spec)
    trace = []
    res = True
    stop = False
    reachable = reachable_states(model)
    not_property = reachable.diff(bddspec)
    nps = model.pick_all_states(not_property)
    for np in nps:
        print("Not property: ", np.get_str_values())
    reached = pynusmv.dd.BDD.false()
    np_reached = pynusmv.dd.BDD.false()
    depth = 0
    np_init = model.init.intersection(not_property)
    state = np_init
    state_s = model.pick_all_states(state)
    for s in state_s:
        print(depth," - State: ", s.get_str_values())
    while not(isEmpty(model, state.diff(reached))) and not(stop):
        depth += 1
        reached = reached.union(state)
        np_state = model.post(state).intersection(not_property)
        state = np_state.intersection(reachable)
        '''
        state = model.post(state)
        '''
        state_s = model.pick_all_states(state)
        for s in state_s:
            print(depth,"- State: ", s.get_str_values())
        np_reached = state.intersection(reached)
        if not(isEmpty(model, np_reached)):
            stop = True
            res = False
            print("Final state: ", model.pick_one_state(np_reached).get_str_values())
            state = model.pick_one_state(np_reached)
            trace.append(state.get_str_values())
            while not(isEmpty(model, state.diff(np_init))):
                np_state = model.pre(state)
                np_state = np_state.intersection(reachable).intersection(not_property)
                inp = model.get_inputs_between_states(np_state, state)
                inp_i = model.pick_one_inputs(inp)
                state = model.pre(state, inp_i)
                state_s = model.pick_one_state(state)
                inp_i = model.pick_one_inputs(inp)
                trace.insert(0, inp_i.get_str_values())
                trace.insert(0, state_s.get_str_values())

    print("My eventually is: ", res)
    print("My trace is: ", trace)
    res, trace = pynusmv.mc.check_explain_ltl_spec(ltlspec)
    return res, trace

def check_explain_always(spec):
    ltlspec = pynusmv.prop.g(spec)
    print("always ltlspec: ", ltlspec)
    model = pynusmv.glob.prop_database().master.bddFsm
    bddspec = spec_to_bdd(model, spec)
    trace = []
    res = True
    reachable = reachable_states(model)
    not_property = reachable.diff(bddspec)    
    if not(isEmpty(model, not_property)):
        res = False
        bad_state = model.pick_one_state(not_property)
        trace.append(bad_state.get_str_values())
        state = bad_state
        # add in 'trace' the elements - states and inputs - from init state to 'bad_state'
        while not(isEmpty(model, state.diff(model.init))):
            np_state = model.pre(state)
            np_state = np_state.intersection(reachable)
            inp = model.get_inputs_between_states(np_state, state)
            inp_i = model.pick_one_inputs(inp)
            state = model.pre(state, inp_i)
            state_s = model.pick_one_state(state)
            trace.insert(0, inp_i.get_str_values())
            trace.insert(0, state_s.get_str_values())
        state = bad_state
        reached = pynusmv.dd.BDD.false()
        # add in 'trace' the elements - states and inputs -  from 'bad_state' to "final" state (e.g. repeated element in a cycle)
        while not(isEmpty(model, state.diff(reached))):
            reached = reached.union(state)
            np_state = model.post(state)
            np_state = np_state.intersection(reachable)
            inp = model.get_inputs_between_states(state, np_state)
            inp_i = model.pick_one_inputs(inp)
            state = model.post(state, inp_i)
            state_s = model.pick_one_state(state)
            trace.append(inp_i.get_str_values())
            trace.append(state_s.get_str_values())
    return res, trace


if len(sys.argv) != 2:
    print("Usage:", sys.argv[0], "filename.smv")
    sys.exit(1)

pynusmv.init.init_nusmv()
filename = sys.argv[1]
pynusmv.glob.load_from_file(filename)
pynusmv.glob.compute_model()
invtype = pynusmv.prop.propTypes['Invariant']
for prop in pynusmv.glob.prop_database():
    spec = prop.expr
    if prop.type == invtype:
        print("Property", spec, "is an INVARSPEC.")
        res, trace = check_explain_eventually(spec)
        if res == True:
            print("Spec is eventually true")
        else:
            print("Spec is not eventually true")
            print(trace)
        '''
        res, trace = check_explain_always(spec)
        if res == True:
            print("Spec is always true")
        else:
            print("Spec is not always true")
            print(trace)
        '''
    else:
        print("Property", spec, "is not an INVARSPEC, skipped.")

pynusmv.init.deinit_nusmv()