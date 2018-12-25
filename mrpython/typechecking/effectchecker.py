import argparse
import ast
import astunparse
import prog_ast
from prog_ast import *

# taken from https://stackoverflow.com/questions/13620542/detecting-empty-function-definitions-in-python
def is_empty_function(func):
    def empty_func():
        pass

    def empty_func_with_doc():
        """Empty function with docstring."""
        pass

    return func.__code__.co_code == empty_func.__code__.co_code or \
        func.__code__.co_code == empty_func_with_doc.__code__.co_code




arg_parser = argparse.ArgumentParser(
                        description='CFG generator for Python files.')

class CFG(object):
    """docstring fo CFG."""
    def __init__(self, file = None):
        super(CFG, self).__init__()
        self.arg = arg
        self.cfgs = []
        self.program = Program()
        if file:
            self.program.build_from_file(file)

    def build(self):
        for name, node in self.program.functions.items():
            print("Computing BB")
            print("head :" + repr(node.body[0]))
            print("tail :" + repr(node.body[-1]))
            bb = to_cfg_FunctionDef(node)
            reset_handled_flag(bb)
            bb = aggregate_basicBlocks(bb)
            reset_handled_flag(bb)
            to_dot_format(bb, 0, name = name)




class BasicBlock(object):
    """docstring for BasicBlock."""

    def __init__(self):
        super(BasicBlock, self).__init__()
        try:
            BasicBlock.bb_index += 1
        except AttributeError:
            BasicBlock.bb_index = 0

        self.index = BasicBlock.bb_index
        self.successors = set()
        self.predecessors = set()
        self.statements = []
        self.btype = "empty"
        self.is_handled = False

    def add_statement(self, st):
        self.statements.append(st)

    def add_successor(self, bb):
        if self.btype == 'return':
            return None
        self.successors.add(bb)
        bb.add_predecessor(self)

    def add_predecessor(self, bb):
        self.predecessors.add(bb)

    def has_successors(self):
        return len(self.successors) > 0

    def get_name(self):
        return "BB"+str(self.index)

    def __str__(self):
        ret_str = ""
        for st in self.statements:
            if isinstance(st, prog_ast.While):
                ret_str += "while "+ astunparse.unparse(st.ast.test)
            elif isinstance(st, prog_ast.For):
                #print(astpp.dump(st.ast))
                ret_str += "for ()"
            elif isinstance(st, prog_ast.If):
                ret_str += "if "+ astunparse.unparse(st.ast.test)
            else:
                ret_str += astunparse.unparse(st.ast)+"\\n"
        return ret_str






def to_cfg_FunctionDef(func_def):
    # Node is not a function definition or it is with an empty body
    if not isinstance(func_def, prog_ast.FunctionDef) or not func_def.body:
        return None

    # Iterate statements and calculate the CFG for each encountred statement
    # inside the function body
    __function_cfg, _ = compute_cfg_for_statements(func_def.body)

    return __function_cfg

def compute_cfg_for_statements(st_list):
    __previous_bb = __head_bb = __tail_bb = None
    for st in st_list:

        st_cfg = compute_cfg_for_statement(st)

        if __head_bb is None:
            __head_bb = st_cfg
        if __previous_bb is not None:
            # link statements CFGs together
            if __previous_bb.btype == 'if-then' or __previous_bb.btype == 'if-then-else':
                # Reestablish once the method 'find_last_empty__basicBlock' is checked
                reset_handled_flag(__previous_bb)
                __previous_bb = find_last_empty__basicBlock(__previous_bb)
                __previous_bb.add_successor(st_cfg)
            elif __previous_bb.btype == 'return':
                if st is st_list[-1]:
                    print("Possible dead code portion ...")
            else:
                #st_cfg.add_predecessor(__previous_bb)
                __previous_bb.add_successor(st_cfg)

        __tail_bb = st_cfg
        __previous_bb = st_cfg
    return __head_bb, __tail_bb

def compute_cfg_for_statement(st):
    if isinstance(st, prog_ast.If):
        __empty_bb = BasicBlock()
        __empty_bb.btype = "empty"
        __if_bb = BasicBlock()
        __if_bb.btype = "if-then"
        __if_bb.add_statement(st)
        cfg__if_body__head, cfg__if_body__tail = compute_cfg_for_statements(st.body)
        cfg__else_body__head = cfg__else_body__tail = None
        __if_bb.add_successor(cfg__if_body__head)
        # If-then-else statement
        if st.orelse:
            __if_bb.btype = "if-then-else"
            cfg__else_body__head, cfg__else_body__tail = compute_cfg_for_statements(st.orelse)
            __if_bb.add_successor(cfg__else_body__head)
            cfg__else_body__tail.add_successor(__empty_bb)
        # If-then statement
        else:
            __if_bb.add_successor(__empty_bb)
        cfg__if_body__tail.add_successor(__empty_bb)
        return __if_bb

    elif isinstance(st, prog_ast.While) or isinstance(st, prog_ast.For):
        __loop_bb = BasicBlock()
        __loop_bb.btype = 'while' if isinstance(st, prog_ast.While) else 'for'
        __loop_bb.add_statement(st)
        cfg__loop_body__head, cfg__loop_body__tail = compute_cfg_for_statements(st.body)
        __loop_bb.add_successor(cfg__loop_body__head)
        cfg__loop_body__tail.add_successor(__loop_bb)
        return __loop_bb
    else:
        __single_bb = BasicBlock()
        if isinstance(st, prog_ast.Return):
            __single_bb.btype = "return"
        else:
            __single_bb.btype = "other"
        __single_bb.add_statement(st)
        return __single_bb

# Re-check the logic
def find_last_empty__basicBlock(bb):
    if bb.is_handled:
        return None
    if bb.btype == "empty":
        return bb
    if not bb.successors:
        return None
    else:
        __empty_bb_lookup = []
        if not bb.is_handled:
            bb.is_handled = True
            for next_bb in bb.successors:
                __empty_bb_lookup.append(find_last_empty__basicBlock(next_bb))

            retr_bb = None
            for block in __empty_bb_lookup:
                if block:
                    retr_bb = block
            return retr_bb

def set_of_basicBlocks(bb, bb_set = set()):
    bbs = bb_set
    if bb not in bbs:
        bbs.add(bb)
    else:
        return bbs
    for succ in bb.successors:
        for x in set_of_basicBlocks(succ, bbs):
            bbs.add(x)
    if bbs == bb_set:
        return bbs

def aggregate_basicBlocks(bb, bb_set = set()):
    retr = bb_set
    if not bb.successors:
        return None
    elif len(bb.successors) == 1 and bb.btype != 'return':
        bb.is_handled = True
        for succ in bb.successors.copy():
            if len(succ.predecessors) == 1:
                for st in succ.statements:
                    bb.add_statement(st)
                for s in succ.successors:
                    bb.add_successor(s)
                bb.successors.remove(succ)
                del succ

    for succ in bb.successors:
        if not succ.is_handled:
            aggregate_basicBlocks(succ)

    return bb

def reset_handled_flag(bb):
    bb_set = set_of_basicBlocks(bb)
    for block in bb_set:
        block.is_handled = False

def to_dot_format(cfg, offset = 0, dot = None, name = ''):
    from graphviz import Digraph
    if offset == 0:
        dot = Digraph(comment='CFG', filename = name, graph_attr={'label': name}, node_attr={'shape': 'square'})
    cfg.is_handled = True
    for bb in cfg.successors:
        dot.node(cfg.get_name(), str(cfg))
        dot.node(bb.get_name(), str(bb))
        dot.edge(cfg.get_name(), bb.get_name())
        if not bb.is_handled:
            to_dot_format(bb, offset+1, dot)

    if offset == 0:
        dot.render(view=True)
        return dot






def check_file_extensions(filename, extensions = ('.py')):
    if (not filename.lower().endswith(extensions)):
        arg_parser.error("file doesn't end with one of {}".format(extensions))
    return filename


if __name__ == '__main__':
    import argparse;
    from astpp import *

    arg_parser.add_argument('file',
                            type =lambda s:check_file_extensions(s),
                            help = "Generate a control flow graph for the given file")

    args = arg_parser.parse_args()

    if args.file is not None:
        cfg = CFG(args.file)
        cfg.build()
    else:
        print('Oh well ; No args, no problems')
