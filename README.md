# Cyber-Physical_Systems

Project for the course of 'Formal Methods for Cyber-Physical Systems' at the University of Padua.

The objective of the project is to define and implement a symbolic algorithm for the verification of simple LTL formulas of "eventually" and "always" type, using BDDs as data structure to represent and manipulate regions.

The attached simple_mc.smv file contains an example python script that uses NuSMV's pynusmv library and model checking algorithms to verify LTL formulas in the form F spec and G spec, where spec is a Boolean formula without temporal operators.

Using the simple_mc.smv script as a starting point, you are asked to reimplement the check_explain_eventually(spec) and check_explain_always(spec) functions without using the algorithms already present in NuSMV, so that they meet the following specifications:

- given spec INVARSPEC type, the check_explain_eventually(spec) function determines whether or not the loaded SMV model meets the LTL F spec formula
- given spec INVARSPEC type, the check_explain_always(spec) function determines whether or not the loaded SMV model meets the LTL G spec formula
- the return value is a tuple where the first element is True and the second element is None if all executions of the loaded SMV model meet the formula. Otherwise, the first element is False and the second element is an SMV model execution that violates the formula.
- the counter-example is a tuple or list that alternates between states and inputs, starting and ending with a state. The counterexample is cyclic if the last state repeats somewhere in the sequence. The states and inputs are represented by the dictionaries where the keys are variables of the SMV model and the values are the value of the variables.

You can find more information about the pynusmv library on the websites http://lvl.info.ucl.ac.be/Tools/PyNuSMV and https://pynusmv.readthedocs.io. 

The library consists of several modules. Only the following modules can be used to implement the project:

- init
- glob
- fsm, excluding reachable_states method
- prop
- dd
