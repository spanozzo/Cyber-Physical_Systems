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
    
def check_explain_eventually(spec):
    ltlspec = pynusmv.prop.f(spec)
    print("eventually ltlspec: ", ltlspec)
    model = pynusmv.glob.prop_database().master.bddFsm
    bddspec = spec_to_bdd(model, spec)
    trace = []
    res = True
    reachable = reachable_states(model)
    not_property = reachable.diff(bddspec)
    init = not_property.intersection(model.init)
    if(isEmpty(model, init)):
        return True, []
    res = False
    init = model.pick_one_state(init)
    trace.append(init.get_str_values())
    state = init
    reached = pynusmv.dd.BDD.false()
    # add in 'trace' the elements - states and inputs -  from 'init' to "final" state (e.g. repeated element in a cycle)
    # return True if a state that satisfy the property is found 
    while not(isEmpty(model, state.diff(reached))):
        reached = reached.union(state)
        np_state = model.post(state).intersection(not_property)
        if (isEmpty(model, np_state)):
            return True, []
        inp = model.get_inputs_between_states(state, np_state)
        inp_i = model.pick_one_inputs(inp)
        state = model.post(state, inp_i)
        state_s = model.pick_one_state(state)
        trace.append(inp_i.get_str_values())
        trace.append(state_s.get_str_values())
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
        res, trace = check_explain_always(spec)
        if res == True:
            print("Spec is always true")
        else:
            print("Spec is not always true")
            print(trace)
    else:
        print("Property", spec, "is not an INVARSPEC, skipped.")

pynusmv.init.deinit_nusmv()