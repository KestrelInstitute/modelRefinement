from xmvTransformer import *
from backend import *
import re

DBG2 = False
def extract_control_vars(xmv_text):
    # Matches lines like: u : ... ; -- ##CONTROL##
    pattern = re.compile(r'^\s*([a-zA-Z_][a-zA-Z0-9_]*)\s*:[^;]*;.*##CONTROL##', re.MULTILINE)
    return pattern.findall(xmv_text)

if __name__ == "__main__":
    """read the input xmv file"""
    if len(sys.argv) < 2:
        print("Usage: python smv2mr.py <inputfile.smv>. To redirect output optionally add \"> <outputfilename> 2> <debug output>\"")
        sys.exit(1)
    input_filename = sys.argv[1]
    with open(input_filename) as f:
        xmv_text = f.read()
    control_var_names = extract_control_vars(xmv_text)
    # print('control_var_names', control_var_names)

    # parser = Lark(smv_grammar, parser="lalr", transformer=SMVTransformer())
    """create a lark parser from the given grammar defn"""
    with open("XMVgrammar.lark") as f:
        smv_grammar = f.read()
    parser = Lark(smv_grammar, parser="lalr")

    """parse the given input file to construct parse tree"""
    tree = parser.parse(xmv_text)
    # print(tree.pretty())
    # with open("models/test.smv") as f:
    #     xmv_text = f.read()

    """tranform the parse tree into python structs (dicts)"""
    intermediate = None
    try:
        # intermediate = parser.parse(xmv_text)
        tr = XMVTransformer()
        intermediate = tr.transform(tree)
    except Exception as e:
        print("***transforming to intermediate form failed:***", e)

    # import pprint
    # pprint.pprint(intermediate)

    """call the backend to generate mr model def"""
    if intermediate != None:
        if DBG2: print(type(intermediate), file=sys.stderr)
        print(smvToPython(intermediate, control_var_names))