import re
from itertools import combinations

def eliminate_implication(formula):
    # Eliminate implication: (p ⇒ q) → (¬p ∨ q)
    formula = re.sub(r'\((.?) ⇒ (.?)\)', r'(¬\1 ∨ \2)', formula)
    # Eliminate biconditional: (p ⇔ q) → (¬p ∨ q) ∧ (¬q ∨ p)
    formula = re.sub(r'\((.?) ⇔ (.?)\)', r'(¬\1 ∨ \2) ∧ (¬\2 ∨ \1)', formula)
    return formula

def move_negation_inward(formula):
    # Move negation inward (DeMorgan Law)
    # ¬(p ∧ q) → (¬p ∨ ¬q)
    formula = re.sub(r'¬\((.?) ∧ (.?)\)', r'(¬\1 ∨ ¬\2)', formula)
    # ¬(p ∨ q) → (¬p ∧ ¬q)
    formula = re.sub(r'¬\((.?) ∨ (.?)\)', r'(¬\1 ∧ ¬\2)', formula)
    # ¬∀ x p → ∃x ¬p
    formula = re.sub(r'¬∀(.?) (.?)', r'∃\1 ¬\2', formula)
    # ¬∃ x p → ∀x ¬p
    formula = re.sub(r'¬∃(.?) (.?)', r'∀\1 ¬\2', formula)
    # ¬¬p → p
    formula = re.sub(r'¬¬(.*?)', r'\1', formula)
    return formula

def standardize_variable_scope(formula):
    # Standardize variable scope
    # (∀x P( x)) ∨ (∃x Q( x)) → (∀x P( x)) ∨ (∃y Q( y))
    quantifiers = re.findall(r'(∀|∃)(.?)\s(.?)\b', formula)
    variable_map = {}
    for quantifier, var, _ in quantifiers:
        if var not in variable_map:
            variable_map[var] = f'{var}'
    for var, replacement in variable_map.items():
        formula = re.sub(r'\b' + re.escape(var) + r'\b', replacement, formula)
    return formula

def move_quantifiers_left(formula):
    # Move all quantifiers left while preserving their scope
    quantifiers = re.findall(r'(∀|∃)(.*?)\s', formula)
    new_formula = formula
    for quantifier, var in quantifiers:
        new_formula = new_formula.replace(f'{quantifier}{var} ', '')
    new_formula = ' '.join([f'{quantifier}{var}' for quantifier, var in quantifiers]) + ' ' + new_formula
    return new_formula


def convert_to_cnf(formula):
    # Convert to conjunctive normal form
    # p ∨ (q ∧ r) → (p ∨ q) ∧ (p ∨ r)
    formula = re.sub(r'(.?) ∨ \((.?) ∧ (.*?)\)', r'(\1 ∨ \2) ∧ (\1 ∨ \3)', formula)

    # Handle quantified expressions
    quantified_vars = re.findall(r'(∀|∃)(.*?)\s', formula)
    for quantifier, var in quantified_vars:
        subformula_match = re.search(re.escape(quantifier + ' ' + var) + r'\s(.*?)$', formula)
        if subformula_match:
            subformula = subformula_match.group(1)
            if '∨' in subformula:
                disjunctions = subformula.split(' ∨ ')
                for i, disj in enumerate(disjunctions):
                    if quantifier == '∃':
                        new_var = f'{var}_{i}'
                        formula = formula.replace(f'{quantifier}{var} {disj}', f'∃{new_var} {disj.replace(var, new_var)}')
                    elif quantifier == '∀':
                        new_var = f'{var}_{i}'
                        formula = formula.replace(f'{quantifier}{var} {disj}', f'∀{new_var} {disj.replace(var, new_var)}')
    return formula

def skolemization(formula):
    # Skolemization for existential quantifiers
    # ∃y P(A) ∨ Q(y) → P(A) ∨ Q(B)
    # If no universal quantifier occurs before the existential quantifier, replace the variable with a new constant symbol
    skolem_constants = ['A', 'B', 'C', 'D', 'E']  # Define some skolem constants
    existentials = re.findall(r'∃(.?)\s(.?)\b', formula)
    skolemized_formula = formula
    for _, var in existentials:
        if not re.search(re.escape(var), skolemized_formula):  # Corrected regex here
            skolemized_formula = skolemized_formula.replace(f'∃{var}', f'{skolem_constants.pop(0)}')
        else:
            skolemized_formula = re.sub(r'∃(.*?)\s' + re.escape(var), lambda m, v=var: '', skolemized_formula)
    return skolemized_formula







def eliminate_universal_quantifiers(formula):
    # Eliminate universal quantifiers
    # ∀x P(x) ∨ Q(F(x)) → P(x) ∨ Q(F(x))
    formula = re.sub(r'∀(.?)\s(.?)', r'\2', formula)
    return formula

def resolution(propositions):
    # Apply resolution procedure
    clauses = []
    for prop in propositions:
        prop = eliminate_implication(prop)
        prop = move_negation_inward(prop)
        prop = standardize_variable_scope(prop)
        prop = skolemization(prop)
        prop = move_quantifiers_left(prop)
        prop = eliminate_universal_quantifiers(prop)
        prop = convert_to_cnf(prop)
        clauses.extend(clauses_from_formula(prop))

    # Resolution
    while True:
        new_clauses = set()
        n = len(clauses)
        for i, j in combinations(range(n), 2):
            clause_i = clauses[i]
            clause_j = clauses[j]
            resolvents = resolve(clause_i, clause_j)
            if set() in resolvents:
                return True  # Empty clause found, contradiction
            new_clauses.update(resolvents)
        if all(new_clause <= clause for clause in clauses for new_clause in new_clauses):
            return False  # No new clauses generated
        clauses.extend(new_clauses)
        clauses = [clause for clause in clauses if clause not in new_clauses]

def resolve(clause_i, clause_j):
    resolvents = []
    for literal_i in clause_i:
        for literal_j in clause_j:
            if literal_i == '¬' + literal_j or '¬' + literal_i == literal_j:
                resolvent = (clause_i | clause_j) - {literal_i, literal_j}
                resolvents.append(resolvent)
    return resolvents

def clauses_from_formula(formula):
    # Turn conjunctions into clauses in a set
    conjunctions = formula.split('∧')
    clauses = [set(conj.split('∨')) for conj in conjunctions]
    return clauses

def print_propositions_in_cnf(propositions):
    print("Propositions in CNF:")
    for prop in propositions:
        prop = eliminate_implication(prop)
        prop = move_negation_inward(prop)
        prop = move_quantifiers_left(prop)
        prop = standardize_variable_scope(prop)
        prop = skolemization(prop)
        prop = eliminate_universal_quantifiers(prop)
        prop_cnf = convert_to_cnf(prop)
        print(prop_cnf)

# Example knowledge base propositions
propositions = [
    "(p ⇒ q)",
    "(p ⇔ q)",
    "¬(p ∧ q)",
    "¬(p ∨ q)",
    "¬∀x p",
    "¬∃x p",
    "¬¬p",
    "(∀x P(x)) ∨ (∃x Q(x))",
    "(∀x P(x)) ∨ (∃y Q(y))",
    "∀x ∃y P(x) ∨ Q(y)",
    "∀x P(x) ∨ Q(F(x))",
    "p ∨ (q ∧ r)"
]

# Print propositions in CNF form
print_propositions_in_cnf(propositions)

# Check satisfiability using resolution
print("Is the knowledge base satisfiable?", resolution(propositions))