# -*- coding: utf-8 -*-
"""
Created on Fri Jan 10 14:19:04 2020

@author: Justin Robbins
"""

import clingo
import clingo_ast_util as cau
from typing import List
from clingo.ast import ASTType
import argparse

'''
  Observer, collects modeling data when the grounder is run
  This is the only time models and atoms can be saved for later processing.
'''
class Observer():
    def __init__(self, incremental: bool):
        self.incremental = incremental
        self.groundRules = []
        self.atoms = []
        self.idtoRule = {}
    ''' 
      Appends lists containing the ids of the atoms in the head and body into groundRules.
    '''
    def rule(self, choice: bool, head: List[int], body: List[int]) -> None:
        self.groundRules.append([head, body])
    '''
      Deletes the last iteration's data from the observer.
    '''
    def reset_observer(self):
        self.groundRules = []
        self.atoms = []

    '''
      Appends the symbol and its ID into the atoms list.
      Note - The ids of facts are zero. Only non-fact atoms have ids.
      Negative id numbers mean that atom began with a 'not'
    '''
    def output_atom(self, symbol: clingo.Symbol, atom: int) -> None:
        self.atoms.append([symbol, atom])
        if atom != 0:
            self.idtoRule[atom] = symbol

class DualGrounder():
    
    '''
    Initializes DualGrounder's variables
    '''
    def __init__(self):
        self.mainControl = None
        self.mainObserver = Observer(True)
        self.auxControl = None
        self.auxObserver = Observer(True)
        # Program as originally read from source documents
        self.prg = []
        # Base  program parsed from prg. Currently consists of all non-constraint rules.
        self.base = []
        # Constraints constructed to eliminate tested invalid models. Appended to base at the start of a solve cycle.
        self.base_additions = []
        # The atoms created from the last MainGrounder grounding and solving are stored her eto be appended to the program's constraints.
        self.constraint_additions = []
        # The original program's constraint rules are stored here
        self.constraints = []
        # The previous atoms and models produced during grounding are stored here. 
        self.last_main_model = None
        self.last_main_atoms = None
        # This is where the constraints grounded at the end of the cycle are put.
        self.last_grounded_constraints = []
    
    '''
    Reset the auxiliary observer and builds AuxGrounder with the previous MainGrounder atoms.
    '''
    def init_auxControl(self, cargs=['--warn=none']):
        self.auxObserver.reset_observer()
        self.auxControl = clingo.Control(cargs)
        self.auxControl.register_observer(self.auxObserver)
        self.last_aux_model = None
        self.last_aux_atoms = None
        
        trialPRG = self.constraints + self.constraint_additions
    
        with self.auxControl.builder() as b:
                for r in trialPRG:
                    b.add(r)
                    
        self.auxControl.configuration.solve.models=1
    
    '''
    Resets the main observer and MainGrounder with the constraints created in previous cycles.
    '''
    def init_mainControl(self, cargs=['--warn=none']):
        self.mainObserver.reset_observer()
        self.mainControl = clingo.Control(cargs)
        self.mainControl.register_observer(self.mainObserver)
        self.last_main_model = None
        self.last_main_atoms = None
        
        mainatoms = self.base + self.base_additions
        
        with self.mainControl.builder() as b:
            for r in mainatoms:
                #print(r)
                b.add(r)
        self.mainControl.configuration.solve.models=1
    
    def update_mainControl(self, progname, constraintstr):
        self.mainControl.add(progname, [], constraintstr)
        self.mainControl.ground([(progname,[])])
    
    # Created by Brian Hodges, this is fed into the read method to take rules out of ASP programs.
    def arg_read_filter(self, rule):
        '''
        This method should be passed into clingo.parse_program as a callback
        '''
        if cau.is_rule(rule):
            self.prg.append(rule)

    # Created by Brian Hodges, this is called to read a string into a program.
    def read(self, program):
        '''
        Takes a program as a string and reads it into a string list
        '''
        clingo.parse_program(program, self.arg_read_filter)
        return self.prg
    
    # This method is used to read programs into a list passed via parameter.
    def read_ext(self, program, output):
        '''
        Takes a program as a string and reads it into the given String list
        '''
        clingo.parse_program(program, (lambda rule : output.append(rule) if cau.is_rule(rule) else None))
    
    def split_filter(self, rule):
        '''
        This method should be passed into clingo.parse_program as a callback
        
        Written by Brian Hodges
        Modified by Justin Robbins
        '''
        
        if cau.is_rule(rule) and str(cau.get_head_literals(rule)[0]) == '#false':
            self.constraints.append(rule)
        else:
            self.base.append(rule)
            
    def split(self, program):
        '''
        Takes a program as a string and separates it into a base and lazy constraints
        Returns a tuple of the base program and constraints as lists of parsed rules
        (base, constrints)
        
        Written by Brian Hodges
        '''
        #print(program)
        clingo.parse_program(program, self.split_filter)
        return self.base, self.constraints
    
    '''
    These callback methods are used to retain solving information that can only be obtained
        via callback methods during the solving process.
    '''
    def main_callback(self, model):
        self.last_main_model = model.symbols(shown=True)
        self.last_main_atoms = model.symbols(atoms=True)
        self.on_model(model)
    
    '''
      Used by callback methods to print the solved model.
    '''
    def on_model(self, m):
        dprint(m)
        
    '''
       Transforms the passed list of constraint rules into a list of non-constraint rules that will be grounded 
           iff the original constraint rule it's created from would be violated.
           
       For example: the constraint rule:
           
           :- in(X), in(Y), r(X,Y), X!=Y.
           
       Would be transformed into:
           
           in'0_in'1_r'01'(X,Y) :- in(X), in(Y), r(X,Y), X!=Y.
           
       This is done to allow us to reconstruct violated constraints post grounding from the AuxGrounder's solving answer set.
    '''
    def constraints_to_ndj_rules(self, constraints):
        prgstr = ""
        # For each rule in the given rules list,
        for c in constraints:
            headpred = []
            body = []
            args = []
            # Collect the arguments of the rule
            # If it is a constraint rule,
            if cau.is_rule(c) and str(cau.get_head_literals(c)[0]) == '#false':
                # For each body literal in the constraint rule,
                for lit in c.body:
                    if lit.atom.type in [ASTType.SymbolicAtom, ASTType.Function, ASTType.Literal]:
                        for arg in cau.get_arguments(lit):
                            if arg not in args:
                                args.append(arg)
            else:
                continue
            
            if len(args) > 10:
                # Too many arguments to encode
                print("Too many argument to encode in constraint" + str(c) + ".")
                continue
            
            # After collecting arguments create rule.
            # For each literal in the body,
            for lit in c.body:
                # Add literal to transformed rule's body.
                body.append(str(lit))
                if lit.atom.type in [ASTType.SymbolicAtom, ASTType.Function, ASTType.Literal]:
                    # If literal is transformable, transform to add to the head of the transformed rule.
                    headstr = ""
                    
                    # Add not to pred string if needed
                    if not cau.is_positive(lit):
                        headstr += "not'"
                    
                    # Add the literal's predicate name to its head representation
                    lpred = cau.get_predicate_symbol(lit)
                    headstr += lpred.name() + "'"
                    
                    # Add numbers corresponding to the literal's argument's indices in the args list
                    for arg in cau.get_arguments(lit):
                        idx = args.index(arg)
                        headstr += str(idx)
                    
                    # Append literal's head representation to the list of all of them.
                    headpred.append(headstr)
            
            headargs = "(" + ",".join(str(arg) for arg in args) + ")"
            new_rule = "_".join(headpred) + "'" + headargs + ":-" + ",".join(body) + "."
            prgstr += new_rule
            #print(new_rule)
        
        self.constraints = []
        #Read transformed rules into AST rules for AuxGrounding
        self.read_ext(prgstr, self.constraints)

    '''
        Given a clingo Symbol that represents an atom,
            this method produces a string version of it.
    '''
    def atom_to_str(self, symbol: clingo.Symbol):
        rule_str = ""
        rule_str += symbol.name
        rule_str += "("
        rule_str += (",".join([str(arg) for arg in symbol.arguments]))
        rule_str += ")."
        return rule_str
    
    '''
        Transforms the answer set of the last MainGrounder grounding into a set of atoms
        that are to be appended with the constraints of the original program.
    '''
    def build_aux_additions(self):
        self.constraint_additions = []
        prgstr = ""
        for atom in self.last_main_atoms:
            strRule = self.atom_to_str(atom)
            prgstr += strRule
        
        self.read_ext(prgstr, self.constraint_additions)
    
    '''
        Traverses the last aux grounding for atoms ending in '
        These grounded atoms indicated a transformed constraint was grounded.
        The list of all such grounded constraints is recorded and returned.
    '''
    def extract_grounded_aux_constraints(self):
        #If rule's name ends in a ' the rule is a grounded constraint.
        grounded_constraints = []
        for [sym,idn] in self.auxObserver.atoms:
            #print(sym)
            if sym.name[-1] == "'":
                grounded_constraints.append(sym)
        self.last_grounded_constraints = grounded_constraints
        return grounded_constraints
    
    '''
        Given a set of grounded heads, this method creates grounded constraints based on the grounded atoms.
        
        Example constraint decoding:
            
            not'line'01_not'line'10_v'0_v'1'(a,b)
            
        Will produce the grounded constraint:
            
            :- not line(a,b), not line(b,a), v(a), v(b).
    '''
    def build_base_additions(self):
        allcstr = ""
        
        if self.last_grounded_constraints:
            for c in self.last_grounded_constraints:
                #print("\nConsidering grounded constraint: " + str(c))
                bodylits = []
                # Get constraint's predicate and arguments
                pred = c.name
                args = [str(arg) for arg in c.arguments]
                
                lits = pred[:-1].split("_")
                # Produce body literals of the new constraint
                for lit in lits:
                    litstr = lit
                    litbodystr = ""
                    if lit[:4] == "not'":
                        litstr = litstr[4:]
                        litbodystr  += "not "
                    
                    lpred, largs = litstr.split("'")
                    # Add predicate to body literal
                    litbodystr += lpred
                    
                    # Add arguments to body literal
                    argids = [int(char) for char in largs]
                    argstrs = []
                    for idn in argids:
                        argstrs.append(args[idn])
                    
                    litbodystr += "(" + ",".join([str(arg) for arg in argstrs]) + ")"
                    #print(litbodystr)
                    
                    # Add body literal to the list of all body literals for this constraint
                    bodylits.append(litbodystr)
                    
                # Construct constrain and add to string of constraints
                cstr = ":-" + ",".join(bodylits) + "."
                allcstr += cstr
        
        #print(allcstr)
        constraints = []
        #self.read_ext(allcstr, constraints)
        return allcstr
        #return constraints

def dprint(message):
    if args.debugprint:
        print(message)
               
'''
    DualGrounder first must be given a program to read, which is divided into programs composed of constraint and non-constraint rules.
    The constraint rules are transformed into disjunctive rules to aid in grounded constraint construction.

    MainGrounder - Nonconstraint rules
    AuxGrounder - Constraint rules

    After initialization, DualGrounder runs a cycle until either MainGrounder runs out of candidate models or a model is found that can be 
        grounded with the AuxGrounder's constraints.
    
    1. Initialize MainGrounder with the constraints created during previous cycles.
    
    2. Ground and solve the resulting program, producing a model to be passed to the AuxGrounder.
        - If a model isn't produced, adding more constraints will not make a new one. 
            The program aborts and reports that the original program has no answer sets.
            
    3. Process MainGrounder's model into atoms. The union of these atoms and the original program's constraint rules 
        fed into AuxGrounder for solving. 
        
    4. The AuxGrounder is grounded. The resulting grounding is processed.
        a. If any transformed constraints were grounded, the grounded constraints are added 
            to the set of constraints that are added into the MainGrounder.
        b. If no transformed constraints were grounded, the answer set that satisfied 
            both the main program and constraint program is returned as the program's answer set.
'''
def main():
    global args
    parser = argparse.ArgumentParser()
    parser.add_argument('files', nargs='+', help='The files to process')
    parser.add_argument('--iterlim', nargs='?', default=0, type=int, help='The maximum number of iterations the system may use. Default does not limit the system.')
    parser.add_argument('--debugprint', action='store_true', default=False, help='Whether or not the system prints runtime data.')
    parser.add_argument('--splitprog', action='store_true', default=False, help='If true, the system will load the first program files into the main grounder and the last into the auxgrounder. Last program should be exclusively constraint rules.')
    parser.add_argument('--wasplike', action='store_true', default=False, help='If true, the system will use wasp-like heuristics for its clingo solving.')
    args = parser.parse_args()
    
    dg = None
    
    if not args.splitprog:
        '''Combine text files and separate constraints into AuxGrounder. Default Behavior.'''
        '''read program text from input files'''
        program = ''
        for filename in args.files:
            with open(filename, 'r') as f:
                program += f.read() + '\n\n' 
        
        dg = DualGrounder()
        dg.read(program)
        
        '''Split read program into non-constraint and constraint rules.'''
        base, constraints = dg.split(program)
        
        '''Transform constraints into disjunctive rules'''
        dg.constraints_to_rules(constraints)
    else:
        '''Puts files into MainGrounder and the last into AuxGrounder. The last file must be exclusively constraint rules.'''
        mainprogram = ''
        auxprogram = ''
        i = 0
        for filename in args.files:
            with open(filename, 'r') as f:
                if i+1 < len(args.files):
                    mainprogram += f.read() + '\n\n' 
                else:
                    auxprogram += f.read() + '\n\n'
            i += 1
        
        dg = DualGrounder()
        mainprglst = []
        dg.read_ext(mainprogram, mainprglst)
        
        auxprglst = []
        dg.read_ext(auxprogram, auxprglst)
        
        '''Ensure given rules are valid'''
        dg.prg = mainprglst + auxprglst
        
        for rule in mainprglst:
            if not cau.is_rule(rule):
                print("Invalid rule given in main input program! Exiting...")
                exit()
        
        dg.base = mainprglst
        
        '''Ensure secondary rules are valid constraints'''
        for rule in auxprglst:
            if not cau.is_rule(rule) or not str(cau.get_head_literals(rule)[0]) == '#false':
                print("Invalid or non-constraint rule given in a secondary input program! Exiting...")
                exit()
                
        dg.constraints = auxprglst
        
        '''Transform constraints into disjunctive rules'''
        dg.constraints_to_ndj_rules(auxprglst)
    
    # Use wasplike args for clingo if specified.
    cargs = ['--warn=none']
    if args.wasplike:
        cargs = ['--warn=none', '--trans-ext=no', '--eq=0', '--sat-prepro=2', '--heuristic=Vsids', '--no-init-moms', '--sign-def=neg', '--rand-freq=no', '--update-lbd=glucose', '--restarts=D,10000,0.8', '--block-restarts=10000,1.4,2000', '--deletion=sort,50,mixed', '--del-glue=4']
    
    # Initialize cycle values
    iterint = 0
    lim = args.iterlim
    if lim == 0:
        lim = float("inf")
    
    
    dprint("\nMain Program:")
    dprint(dg.base)
    
    dprint("\nAux Program:")
    dprint(dg.constraints)
    '''
    import sys
    sys.exit("Rule test over.")
    '''
    dg.init_mainControl(cargs)
    lastcstr = ""
    while(True):
        dprint("\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
        '''
            Initialize MainGrounder with base program and past generated constraints.
            Grounds and solves the resulting program.
        '''
        dprint("Iteration " + str(iterint) + ": ")
        
        dprint("\nBase Program w/ Additions: ")
        dprint(dg.base + dg.base_additions)
        
        if iterint != 0:
            dg.update_mainControl("Iteration_" + str(iterint-1), lastcstr)
        else:
            dg.mainControl.ground([("base",[])])
        
        dprint("\nMain Solving:")
        dg.mainControl.solve(on_model=dg.main_callback)
        
        dprint("\nMain Program Answer Set:")
        dprint(dg.last_main_atoms)
        
        '''
            If no answer set has been generated by the MainGrounder, there is no answer 
                set that satisfies both parts of the original program.
        '''
        if dg.last_main_model == None:
            dprint("\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
            print("Ran out of models, aux constraints not satisified.")
            dprint("")
            break
        
        '''
            Builds Aux program from the transformed constraints and the atoms in the main program's answer set.
            The resulting program is them grounded and solved.
        '''
        dg.build_aux_additions()
        dg.init_auxControl(cargs)
        
        dprint("\nAux Program: ")
        dprint(dg.constraints)
        
        dprint("\nConstraint Program w/ Additions:")
        dprint(dg.constraints + dg.constraint_additions)
        
        dg.auxControl.ground([("base",[])])
        
        dprint("\nAux Observer Atoms:")
        dprint(dg.auxObserver.atoms)
        
        dg.extract_grounded_aux_constraints()
        
        '''
            If none of the transformed constraints were grounded, 
            an answer set for both sub programs has been found, and the program exits returning this model.
        '''
        if not dg.last_grounded_constraints:
            dprint("\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
            dprint("")
            print("\nSolution found after " + str(iterint) + " iterations:")
            print(dg.last_main_model)
            dprint("")
            break
        
        '''
            If a solution wasn't found, constraints are generated to eliminate the failed answer set from the MainGrounder.
        '''
        lastcstr = dg.build_base_additions()
        dprint("\n Generated constraint program")
        dprint(lastcstr)
        '''
        for c in dg.build_base_additions():
            dprint("\ninserting:")
            dprint(c)
            addedconstraintcount += 1
            dg.base_additions.append(c)
        dprint("Current number of added constraints: " + str(addedconstraintcount))
        '''
        '''
            System to preemptively end the DualGrounder after a prespecified amount of cycles.
        '''
        iterint += 1
        if iterint >= lim:
            dprint("\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~")
            print("Breaking loop after " + str(iterint) + " iterations.")
            print(dg.last_main_model)
            break
    
if __name__ == '__main__':
    main()