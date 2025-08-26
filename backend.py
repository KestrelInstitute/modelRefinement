
"""takes the intermediate form (python dicts) and produces python model def for input to mr v5"""
def smvToPython(parsed,control_var_names):
    out = []
    
    module_name = parsed['module']
    sections = {k: v for sec in parsed['sections'] for k, v in sec.items()}

    # Build type dictionaries for control and environment variables
    control_var_types = {}
    env_var_types = {}

    # Get variable type info from parsed model
    var_decls = {d['name']: d['type'] for d in sections.get('VAR', [])}
    ivar_decls = {d['name']: d['type'] for d in sections.get('IVAR', [])}
    vars_ = [d['name'] for d in sections.get('VAR', [])]
    ctrl_vars = [v for v in vars_ if v in control_var_names]
    ivars = [d['name'] for d in sections.get('IVAR', [])]

    for v in ctrl_vars:
        control_var_types[v] = var_decls[v]
    for v in ivars:
        env_var_types[v] = ivar_decls[v]

    state_var_names = [v for v in vars_ if v not in control_var_names]
    funs  = sections.get('FUN', [])
    trans = sections.get('TRANS', [])
    # invar_expr = sections.get('INVAR', "True")
    invar_expr = sections.get('INVAR', True)
    ltlspec = sections.get('LTLSPEC', {"name": "unnamed", "expr": "True"})["expr"]

    # Z3 variable declarations
    # state_decls = ", ".join(f"{v}, {v}X" for v in vars_)
    out.append("from z3 import *")
    out.append("from types import SimpleNamespace\n")
    out.append(f"#  state variables")
    state_decls = ", ".join(f"{v}, {v}X" for v in state_var_names)
    state_names = " ".join(f"{v} {v}X" for v in state_var_names)   # for the right side
    out.append(f"{state_decls} = Ints('{state_names}')")
    out.append(f"state = [{', '.join(state_var_names)}]")
    out.append(f"stateX = [{', '.join(v + 'X' for v in state_var_names)}]")
    out.append(f"subst = [{', '.join(f'({v},{v}X)' for v in state_var_names)}]")

    # out.append(f"stateInv = {invar_expr}  # SN: where is this used?\n")

    # Env and control vars
    env_and_ctrl_vars = ivars + ctrl_vars
    if env_and_ctrl_vars:
        out.append("# Env, Sys Control variables")
        out.append(", ".join(env_and_ctrl_vars) + f" = Ints('{ ' '.join(env_and_ctrl_vars) }')\n")
    
    # Module node
    out.append("# Nodes")
    out.append("m0 = SimpleNamespace(")
    out.append(f"  name = \"{module_name}\",")
    out.append(f"  vars = state,")
    out.append(f"  postVars = stateX,")
    out.append(f"  subst = subst,")
    out.append(f"  invariant = {formatProp(invar_expr)}")
    out.append(")\n")

    # Transition(s)
    action_lines = []

    for i, t in enumerate(trans):
        name = f"update{i}"
        parts = collectTerms(t, ["and", "or"])
        parts_str = [exprToStr(p) for p in parts]
        # nexts = [p for p in parts_str if "next(" in p]
        # preds = [p for p in parts_str if "next(" not in p]
        nexts = [replaceNexts(p) for p in parts_str if "next(" in p]
        preds = [replaceNexts(p) for p in parts_str if "next(" not in p]
        control_preds = [mkVarConstraint(v, typ) for v, typ in control_var_types.items()]
        env_preds = [mkVarConstraint(v, typ) for v, typ in env_var_types.items()]

        out.append(f"# Arcs/Transitions")
        out.append(f"{name} = SimpleNamespace(")
        out.append(f"    name = \"{name}\",")
        out.append(f"    actionPred = And({', '.join(nexts)}),")
        out.append(f"    envVars = [{', '.join(ivars)}],")
        # out.append(f"    envPred = Or({', '.join(f'{v} == {val}' for v in ivars for val in [0,1,2,3,4])}),")
        if len(env_preds) == 1: 
            out.append(f"    envPred = {env_preds[0]},")
        else:
            out.append(f"    envPred = And({', '.join(env_preds)}),")
        # see earlier ctrl_vars = [v for v in vars_ if v not in ivars]
        out.append(f"    controlVars = [{', '.join(ctrl_vars)}],")
        # out.append(f"    controlPred = Or({', '.join(preds)}),")

        if len(control_preds) == 1: 
            out.append(f"    controlPred = {control_preds[0]},")        
        else:
            out.append(f"    controlPred = And({', '.join(control_preds)}),")
        out.append(f"    precNode = m0,")
        out.append(f"    postNode = m0")
        out.append(")")
        out.append("")

    out.append("transitions = [update0]")
    out.append("")
    out.append("model = SimpleNamespace(")
    out.append("    name = \"FC\",")
    out.append("    initNode = m0,")
    out.append("    nodes = [m0],")
    out.append("    transitions = transitions")
    out.append(")\n")

    """Required props"""
    out.append("# Required Properties")
    out.append("initProps = [buf == 0, out == 0]")
    # out.append(f"safetyProps = [{ltlspec}]")
    # out.append(f"safetyProps = [{exprToStr(ltlspec)}]")
    out.append(f"safetyProps = [{formatProp(ltlspec)}]")

    return "\n".join(out)

# ----------------------------------------------------------------------------
def collectTerms(expr, op_names):
    if isinstance(expr, tuple) and expr[0] in op_names:
        return collectTerms(expr[1], op_names) + collectTerms(expr[2], op_names)
    else:
        return [expr]

def exprToStr(expr):
    if isinstance(expr, tuple):
        op = expr[0]
        #not needed if outputting Z3 style prefix expressions
        # if op == "and":
        #     return f"({exprToStr(expr[1])} & {exprToStr(expr[2])})"
        # if op == "or":
        #     return f"({exprToStr(expr[1])} | {exprToStr(expr[2])})"
        # if op == "not":
        #     return f"!{exprToStr(expr[1])}"
        if op == "compare":
            if expr[1] == "=":
                return f"({exprToStr(expr[2])}=={exprToStr(expr[3])})"
            else:
                return f"({exprToStr(expr[2])} {expr[1]} {exprToStr(expr[3])})"
        if op == "add":
            return f"({exprToStr(expr[1])} + {exprToStr(expr[2])})"
        if op == "sub":
            return f"({exprToStr(expr[1])} - {exprToStr(expr[2])})"
        if op == "mul":
            return f"({exprToStr(expr[1])} * {exprToStr(expr[2])})"
        if op == "div":
            return f"({exprToStr(expr[1])} / {exprToStr(expr[2])})"
        if op == "func":
            name, args = expr[1], expr[2]
            return f"{name}({', '.join(exprToStr(a) for a in args)})"
        if op == "var":
            return str(expr[1])
        if op == "num":
            return str(expr[1])
        return str(expr)
    else:
        return str(expr)

def formatProp(expr):
    if isinstance(expr, tuple):
        op = expr[0]
        if op in {"and", "or"}:
            args = collectTerms(expr, {op})
            args_str = [exprToStr(a) for a in args]
            prefix = "And" if op == "and" else "Or"
            return f"{prefix}({', '.join(args_str)})"
        elif op == "not":
            return f"Not({formatProp(expr[1])})"
        else:
            return exprToStr(expr)
    else:
        return exprToStr(expr)

# def mkVarConstraint(varname, typ):
#     """Generate Z3 constraint string for a variable given its type."""
#     print('---mkVarConstraint: typ', typ)
#     if isinstance(typ['values'], list):  # Enum
#         return f"Or({', '.join(f'{varname} == {v}' for v in typ)})"
#     elif isinstance(typ['values'], tuple):  # Range (nuXmv)
#         return f"And({varname} >= {typ[0]}, {varname} <= {typ[1]})"
#     else:
#         return "True"  # fallback

def mkVarConstraint(varname, typ):
    """Generate Z3 constraint string for a variable given its type."""
    # print('---mkVarConstraint: typ', typ)
    if isinstance(typ, dict):
        if typ["kind"] == "enum":
            vals = typ["values"]
            return f"Or({', '.join(f'{varname} == {v}' for v in vals)})"
        elif typ["kind"] == "range":
            start, end = typ["values"]
            return f"And({varname} >= {start}, {varname} <= {end})"
        else:
            return "True"  # fallback for unknown dict kind
    elif typ == "integer":
        return "True"  # unconstrained integer
    elif typ == "boolean":
        return f"Or({varname} == 0, {varname} == 1)"  # or use True/False as needed
    else:
        return "True"  # fallback for any other type

import re

def replaceNexts(s):
    # Replace next(var) with varX
    return re.sub(r'next\((\w+)\)', r'\1X', s)
# ----------------------------------------------------------------------------