import re
from types import SimpleNamespace
# from model_plan import *
from model_FC import *

init_node = getattr(model, "initNode", model.nodes[0])


def reverseTranslate(model):
    out = []
    out.append("MODULE main")
    out.append("VAR")

    # Gather all variable names
    all_vars = set(getattr(init_node, "vars", []))
    ctrl_vars = list(getattr(model.transitions[0], "controlVars", []))
    env_vars = list(getattr(model.transitions[0], "envVars", []))
    if env_vars == []: env_vars = list(getattr(model.nodes[0], "envVars", []))
    state_vars = [v for v in all_vars if v not in ctrl_vars and v not in env_vars]
    post_vars = list(getattr(init_node, "postVars", []))

    # Build mapping: bufX -> buf, outX -> out
    subst = getattr(init_node, "subst", {})
    postvar_map = buildPostvarNameMap(subst)

    # State variables
    # inv = getattr(init_node, "invariant", "True")
    action_pred = getattr(model.transitions[0], "actionPred", None)
    for v in state_vars:
        # out.append("    " + p red_to_smv_type(v, str(action_pred)))
        # out.append("    " + getXmvType(v, str(action_pred)))
        out.append("    " + getXmvType(getVarName(v), str(action_pred), v))

    # Control variables
    ctrl_pred = getattr(model.transitions[0], "controlPred", "True")
    for v in ctrl_vars:
        # out.append("    " + getXmvType(v, str(ctrl_pred)))
        out.append("    " + getXmvType(getVarName(v), str(ctrl_pred), v))

    # Environment variables
    out.append("IVAR")
    env_pred = getattr(model.transitions[0], "envPred", "True")
    for v in env_vars:
        # out.append("    " + getXmvType(v, str(env_pred)))
        out.append("    " + getXmvType(getVarName(v), str(env_pred), v))

    # Transitions
    out.append("TRANS")
    # action_pred = getattr(model.transitions[0], "actionPred", None)
    if action_pred is not None:
        out.append(f"    {exprToXmv(action_pred, postvar_map)}")

    # Invariant
    invariant = getattr(init_node, "invariant", None)
    if invariant is not None:
        out.append("INVAR")
        out.append(f"    {exprToXmv(invariant, postvar_map)}")

    # LTLSPEC (safetyProps)
    out.append('LTLSPEC\n    G (')
    # for prop in safetyProps:
    #     out.append(f"    {exprToXmv(prop, postvar_map)}")
    out.append(f"        {exprToXmv(safetyProps, postvar_map)}")
    out.append("      )")
    return "\n".join(out)


def getVarName(z3var):
    """Get the name of a Z3 variable or return as string if not Z3."""
    return z3var.decl().name() if hasattr(z3var, "decl") else str(z3var)

def buildPostvarNameMap(subst):
    """Build a mapping from postvar name to prevar name using subst. needed b/c need to replace fooX by next(foo) but need the string map not the variable map"""
    postvar_map = {}
    for prevar, postvar in subst:
        prevar_name = getVarName(prevar)
        postvar_name = getVarName(postvar)
        postvar_map[postvar_name] = prevar_name
    return postvar_map


def getRange(pred, var):
    """Extracts a range from And(var >= L, var <= U)"""
    pred = pred.replace(" ", "")
    m = re.fullmatch(r"And\(%s>=(-?\d+),%s<=(-?\d+)\)" % (var, var), pred)
    if m:
        return m.group(1), m.group(2)
    return None

def getEnum(pred, var):
    """Extracts enum values from Or(var==a, var==b, ...)"""
    pred = pred.replace(" ", "")
    # Find all var==value
    vals = re.findall(rf"{var}==(-?\d+)", pred)
    if vals and pred.startswith("Or("):
        return vals
    return None


def getXmvType(varname, pred, z3var=None):
    """Convert a Z3-style constraint string to SMV/nuXmv type declaration."""
    rng = getRange(pred, varname)
    if rng:
        lo, hi = rng
        if '.' in lo or '.' in hi:
            return f"{varname} : real;"
        else:
            return f"{varname} : {lo} .. {hi};"
    enum_vals = getEnum(pred, varname)
    if enum_vals:
        return f"{varname} : {{{', '.join(enum_vals)}}};"
    # Default: use Z3 type if available
    if z3var is not None:
        sort = getattr(z3var, 'sort', lambda: None)()
        if sort is not None and hasattr(sort, 'name'):
            if sort.name() == 'Real':
                return f"{varname} : real;"
    return f"{varname} : integer;"


def exprToXmv(expr,postvar_map=None):
    # If expr is a list or tuple, treat as conjunction
    if isinstance(expr, (list, tuple)):
        return " & ".join(exprToXmv(e, postvar_map) for e in expr)
    s = str(expr)
    if postvar_map:
        for postvar, statevar in postvar_map.items():
            s = re.sub(rf'\b{re.escape(postvar)}\b', f'next({statevar})', s)
    # Handle And(...) and Or(...) recursively

    def maybeParen(p):
        p = p.strip()
        if p.startswith("And(") or p.startswith("Or("):
            return f"({exprToXmv(p, postvar_map)})"
        return exprToXmv(p, postvar_map)
    
    def prefixToXmvInfix(s, op, smv_op):
        if s.startswith(f"{op}(") and s.endswith(")"):
            inner = s[len(op)+1:-1]
            # Split on commas not inside parentheses
            parts = []
            depth = 0
            last = 0
            for i, c in enumerate(inner):
                if c == '(':
                    depth += 1
                elif c == ')':
                    depth -= 1
                elif c == ',' and depth == 0:
                    parts.append(inner[last:i])
                    last = i+1
            parts.append(inner[last:])
            # return f" {smv_op} ".join(exprToXmv(p.strip()) for p in parts)
            return f" {smv_op} ".join(maybeParen(p) for p in parts)
        return None

    for op, smv_op in [("And", "&"), ("Or", "|")]:
        res = prefixToXmvInfix(s, op, smv_op)
        if res is not None:
            return res

    # Replace == with =, BoolVal(True/False) with TRUE/FALSE
    s = s.replace("==", "=")
    s = s.replace("BoolVal(True)", "TRUE")
    s = s.replace("BoolVal(False)", "FALSE")
    return s


# import re
# def smv_assignments(expr, postvar_map):
#     # Converts 'bufX = buf + e - out & outX = out + u'
#     # to 'next(buf) = buf + e - out & next(out) = out + u'
#     # using postvar_map {postvar: prevar}.
#     s = str(expr)
#     # Pattern for assignments: postvar = rhs
#     def repl_assign(match):
#         lhs = match.group(1).strip()
#         rhs = match.group(2).strip()
#         lhs_new = f"next({postvar_map.get(lhs, lhs)})"
#         return f"{lhs_new} = {rhs}"
#     # Replace all assignments in the string (handles multiple assignments joined by & or |)
#     s = re.sub(r'([a-zA-Z_][a-zA-Z0-9_]*)\s*=\s*([^&|]+)', repl_assign, s)
#     return s


# Example usage:
if __name__ == "__main__":
    # Suppose you have a model object from your backend
    # from models.model_test import model
    print(reverseTranslate(model))
    # pass