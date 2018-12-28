import argparse
import ast
import astunparse
from translate import tr

from typechecking.prog_ast import *


arg_parser = argparse.ArgumentParser(
                        description='CFG generator for Python files.')


class BasicBlock(object):
    """docstring for BasicBlock."""

    def __init__(self):
        super(BasicBlock, self).__init__()

        # Static counter for graphviz labeling purpose
        try:
            BasicBlock.bb_index += 1
        except AttributeError:
            BasicBlock.bb_index = 0
        # Unique ID for each new created basic block
        self.index = BasicBlock.bb_index

        self.successors = set()
        self.predecessors = set()

        # List of statements aggregated in the same basic block
        self.statements = []
        # Type of the basic block, used to distinguish some special blocks
        self.btype = "empty"
        self.is_handled = False
        # Line number of the first statement in the block for reporting purpose
        self.begin_lineno = -1
        # Line number of the last statement
        self.end_lineno = -1

    def add_statement(self, st):
        self.statements.append(st)

    def add_successor(self, bb):
        #
        if self.btype == 'return':
            return None
        self.successors.add(bb)
        # Keep track of predecessors as well
        bb.predecessors.add(self)

    def remove_successor(self, bb):
        # removing a succesor of a block affect the succesor block's predecessors
        # that we just removed
        self.successors.remove(bb)
        bb.predecessors.remove(self)

    def has_successors(self):
        return len(self.successors) > 0
    # Used for graphviz
    def get_name(self):
        return "BB"+str(self.index)
    # Used for reporting errors and warnings
    def get_begin_lineno(self):
        if self.statements:
            self.begin_lineno = self.statements[0].ast.lineno
        return self.begin_lineno

    def get_end_lineno(self):
        if self.statements:
            self.end_lineno = self.statements[-1].ast.lineno
        return self.end_lineno
    # Checks if the last statement in the block is a "Return" statement
    def ends_with_return(self):
        for st in self.statements:
            if isinstance(st, Return):
                return True
        return False
    # Used for graphiz drawing and debugging also
    def __str__(self):
        ret_str = ""
        for st in self.statements:
            if isinstance(st, While):
                ret_str += "while "+ astunparse.unparse(st.ast.test)
            elif isinstance(st, For):
                #print(astpp.dump(st.ast))
                ret_str += "for ()"
            elif isinstance(st, If):
                ret_str += "if "+ astunparse.unparse(st.ast.test)
            elif isinstance(st, ContainerAssign):
                ret_str += astunparse.unparse(st.container_expr.ast) + "[" + \
                           astunparse.unparse(st.container_index.ast) + "]=" + \
                           astunparse.unparse(st.assign_expr.ast)
            else:
                ret_str += astunparse.unparse(st.ast)
        return ret_str



class ImplicitNoneTypeReturnError(TypeError):
    def __init__(self, node):
        self.node = node

    def is_fatal(self):
        return False

    def fail_string(self):
        return "ImplicitNoneTypeReturnError[{}]@{}:{}".format(str(self.node.ast.__class__.__name__)
                                                       , self.node.ast.lineno
                                                       , self.node.ast.col_offset)

    def report(self, report):
        if isinstance(self.node, ContainerAssign):
            report.add_convention_error('error', tr('Not-Python101'), -1, -1
                                        , tr("This function may return None"))
        else:
            report.add_convention_error('error', tr('Not-Python101'), self.node.ast.lineno, self.node.ast.col_offset
                                    , tr("This function may return None"))



def implicit_nonetype_return_check_FunctionDef(fun_def, ctx):
    # Compute the function Control Flow Graph
    fun_cfg = to_cfg_FunctionDef(fun_def)

    if fun_cfg.btype != 'empty':
        reset_handled_flag(fun_cfg)
        fun_cfg = aggregate_basicBlocks(fun_cfg)
    # Convert the graph into a set of blocks
    mark_exit_basicBlocks(fun_cfg)
    cfg_bb = set_of_basicBlocks(fun_cfg, set())


    for bb in cfg_bb:
        if bb.is_exit_bb and not bb.ends_with_return():
            if bb.statements:
                ctx.add_type_error(ImplicitNoneTypeReturnError(bb.statements[len(bb.statements)-1]))
            else:
                ctx.add_type_error(ImplicitNoneTypeReturnError(fun_def.body[-1]))

    reset_handled_flag(fun_cfg)
    to_dot_format(fun_cfg, 0, name = fun_def.name)




def to_cfg_FunctionDef(func_def):
    # Node is not a function definition or it is with an empty body
    if not isinstance(func_def, FunctionDef):
        return None

    # Iterate statements and calculate the CFG for each encountred statement
    # inside the function body
    __function_cfg, _ = compute_cfg_for_statements(func_def.body)

    if __function_cfg.btype != 'empty':
        reset_handled_flag(__function_cfg)
        #__function_cfg = aggregate_basicBlocks(__function_cfg)
        mark_exit_basicBlocks(__function_cfg)
    return __function_cfg

def compute_cfg_for_statements(st_list):
    # May be check if the function body is empty then return a single
    # empty block
    if not st_list:
        empty_block = BasicBlock()
        return empty_block, empty_block
    __previous_bb = __head_bb = __tail_bb = None
    for st in st_list:

        st_cfg = compute_cfg_for_statement(st)

        if __head_bb is None:
            __head_bb = st_cfg
        if __previous_bb is not None:
            # link statements CFGs together
            # Re-check again if it's really necessary to keep this snippet
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
        # We may remove the upper snippet, is this snippet enough???
        if st_cfg.btype == 'if-then' or st_cfg.btype == 'if-then-else':
            reset_handled_flag(st_cfg)
            __tail_bb = __previous_bb = find_last_empty__basicBlock(st_cfg)

        else:
            __tail_bb = __previous_bb = st_cfg
    return __head_bb, __tail_bb

def compute_cfg_for_statement(st):
    if isinstance(st, If):
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

    elif isinstance(st, While) or isinstance(st, For):
        __loop_bb = BasicBlock()
        __loop_bb.btype = 'while' if isinstance(st, While) else 'for'
        __loop_bb.add_statement(st)
        cfg__loop_body__head, cfg__loop_body__tail = compute_cfg_for_statements(st.body)
        __loop_bb.add_successor(cfg__loop_body__head)
        cfg__loop_body__tail.add_successor(__loop_bb)
        return __loop_bb
    else:
        __single_bb = BasicBlock()
        if isinstance(st, Return):
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
        bb_set.add(bb)
    else:
        return bbs
    if bb:
        for succ in bb.successors:
            for x in set_of_basicBlocks(succ, bbs):
                bbs.add(x)
    if bbs == bb_set:
        return bbs

# TODO: Fix issue with stackoverflow for certain functions
def aggregate_basicBlocks(bb, bb_set = set()):
    retr = bb_set
    #print("Handling "+ str(bb))
    with open('out.txt', 'a') as f:
        f.write(str(bb))
    if not bb.successors:
        return bb
    elif (len(bb.successors) == 1 and bb.btype != 'return' and
          bb.btype != 'for' and bb.btype != 'while'
          ):
        bb.is_handled = True
        successors_copy = bb.successors.copy()
        if bb.btype == 'empty':
            for pred in bb.predecessors.copy():
                for s in bb.successors:
                    pred.add_successor(s)
                pred.remove_successor(bb)
            bb = next(iter(bb.successors))
        else:
            for succ in successors_copy:
                if len(succ.predecessors) == 1:
                    for st in succ.statements:
                        bb.add_statement(st)
                    for s in succ.successors.copy():
                        succ.remove_successor(s)
                        bb.add_successor(s)
                    bb.remove_successor(succ)
                    del succ
                # Empty block has exactly one succesor, so we can delete it
                # and link its predecessors to its unique succesor

        # looking for a fixpoint
        if successors_copy != bb.successors:
            print("aggregate_basicBlocks")
            aggregate_basicBlocks(bb)
    # Node can't be aggregated, and it stands alone
    else:
        bb.is_handled = True

    for succ in bb.successors:
        print(succ)
        if not succ.is_handled:
            aggregate_basicBlocks(succ)

    return bb

def mark_exit_basicBlocks(bb):
    bb_set = set_of_basicBlocks(bb, set())
    for block in bb_set:
        block.is_exit_bb = False if block.successors else True


def reset_handled_flag(bb):
    bb_set = set_of_basicBlocks(bb, set())
    for block in bb_set:
        block.is_handled = False

def to_dot_format(cfg, offset = 0, dot = None, name = ''):
    from graphviz import Digraph
    if offset == 0:
        dot = Digraph(comment='CFG', filename = name, graph_attr={'label': name}, node_attr={'shape': 'square'})
    cfg.is_handled = True

    if not cfg.successors and offset == 0:
        if cfg.is_exit_bb:
            dot.node(cfg.get_name(), str(cfg), shape='doublecircle')
        elif cfg.btype == 'if-then' or cfg.btype == 'if-then-else' or \
            cfg.btype == 'while' or cfg.btype == 'for':
            dot.node(cfg.get_name(), str(cfg), shape='Msquare')
        else:
            dot.node(cfg.get_name(), str(cfg))
    else:
        for bb in cfg.successors:
            if cfg.is_exit_bb:
                dot.node(cfg.get_name(), str(cfg), shape='doublecircle')
            elif cfg.btype == 'if-then' or cfg.btype == 'if-then-else' or \
                cfg.btype == 'while' or cfg.btype == 'for':
                dot.node(cfg.get_name(), str(cfg), shape='Msquare')
            else:
                dot.node(cfg.get_name(), str(cfg))

            if bb.is_exit_bb:
                dot.node(bb.get_name(), str(bb), shape='doublecircle')
            elif bb.btype == 'if-then' or bb.btype == 'if-then-else' or \
                bb.btype == 'while' or bb.btype == 'for':
                dot.node(bb.get_name(), str(bb), shape='Msquare')
            else:
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
        print(args.file)
    else:
        print('Oh well ; No args, no problems')
