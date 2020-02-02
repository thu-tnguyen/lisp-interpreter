"""A lisp interpreter and its read-eval-print loop."""
from __future__ import print_function  # Python 2 compatibility

from lisp_builtins import *
from lisp_reader import *
from ucb import main, trace


# Eval/Apply 
def lisp_eval(expr, env, _=None): # Optional third argument is ignored
    """Evaluate lisp expression EXPR in environment ENV.

    >>> expr = read_line('(+ 2 2)')
    >>> expr
    Pair('+', Pair(2, Pair(2, nil)))
    >>> lisp_eval(expr, create_global_frame())
    4
    """
    # Evaluate atoms
    if lisp_symbolp(expr):
        return env.lookup(expr)
    elif self_evaluating(expr):
        return expr

    # All non-atomic expressions are lists (combinations)
    if not lisp_listp(expr):
        raise lispError('malformed list: {0}'.format(repl_str(expr)))
    first, rest = expr.first, expr.second
    if lisp_symbolp(first) and first in SPECIAL_FORMS: 
        return SPECIAL_FORMS[first](rest, env)
    else:        
        procedure = lisp_eval(first, env)
        check_procedure(procedure)
        if isinstance(procedure, MacroProcedure):
            return lisp_eval(procedure.apply_macro(rest, env), env)
        else:
            def helper(expr, env =env):
                return lisp_eval(expr, env)
            return lisp_apply(procedure, rest.map(helper), env)
        

def self_evaluating(expr):
    """Return whether EXPR evaluates to itself."""
    return (lisp_atomp(expr) and not lisp_symbolp(expr)) or expr is None

def lisp_apply(procedure, args, env):
    """Apply lisp PROCEDURE to argument values ARGS (a lisp list) in
    environment ENV."""
    check_procedure(procedure)
    if isinstance(procedure, BuiltinProcedure):
        return procedure.apply(args, env)
    else:
        new_env = procedure.make_call_frame(args, env)
        return eval_all(procedure.body, new_env)

def eval_all(expressions, env):
    """Evaluate each expression in the lisp list EXPRESSIONS in
    environment ENV and return the value of the last."""
    
    if expressions == nil:
        return None
    if len(expressions) == 1:
        return lisp_eval(expressions.first, env, True)
    lisp_eval(expressions.first, env)
    return eval_all(expressions.second, env)

# Environments 

class Frame(object):
    """An environment frame binds lisp symbols to lisp values."""

    def __init__(self, parent):
        """An empty frame with parent frame PARENT (which may be None)."""
        self.bindings = {}
        self.parent = parent

    def __repr__(self):
        if self.parent is None:
            return '<Global Frame>'
        s = sorted(['{0}: {1}'.format(k, v) for k, v in self.bindings.items()])
        return '<{{{0}}} -> {1}>'.format(', '.join(s), repr(self.parent))

    def define(self, symbol, value):
        """Define lisp SYMBOL to have VALUE."""
        
        self.bindings[symbol]=value

    def lookup(self, symbol):
        """Return the value bound to SYMBOL. Errors if SYMBOL is not found."""
        
        if symbol in self.bindings:
            return self.bindings[symbol]
        else:
            if self.parent != None:
                return self.parent.lookup(symbol)
            else:
                raise lispError('unknown identifier: {0}'.format(symbol))
        

    def make_child_frame(self, formals, vals):
        """Return a new local frame whose parent is SELF, in which the symbols
        in a lisp list of formal parameters FORMALS are bound to the lisp
        values in the lisp list VALS. Raise an error if too many or too few
        vals are given.

        >>> env = create_global_frame()
        >>> formals, expressions = read_line('(a b c)'), read_line('(1 2 3)')
        >>> env.make_child_frame(formals, expressions)
        <{a: 1, b: 2, c: 3} -> <Global Frame>>
        """
        

        if len(formals) != len(vals):
            raise lispError('Too many or too few vals are given.')
        
        new_env = Frame(self)
        for i in range(len(formals)):
            new_env.define(formals.first, vals.first)
            formals , vals = formals.second, vals.second

        return  new_env

# Procedures 
class Procedure(object):
    """The supertype of all lisp procedures."""

def lisp_procedurep(x):
    return isinstance(x, Procedure)

class BuiltinProcedure(Procedure):
    """A lisp procedure defined as a Python function."""

    def __init__(self, fn, use_env=False, name='builtin'):
        self.name = name
        self.fn = fn
        self.use_env = use_env

    def __str__(self):
        return '#[{0}]'.format(self.name)

    def apply(self, args, env):
        """Apply SELF to ARGS in ENV, where ARGS is a lisp list.

        >>> env = create_global_frame()
        >>> plus = env.bindings['+']
        >>> twos = Pair(2, Pair(2, nil))
        >>> plus.apply(twos, env)
        4
        """
        if not lisp_listp(args):
            raise lispError('arguments are not in a list: {0}'.format(args))
        # Convert a lisp list to a Python list
        python_args = []
        while args is not nil:
            python_args.append(args.first)
            args = args.second
       
        if self.use_env:
            python_args.append(env)
        try:
            return self.fn(*python_args) 
        except:
            raise lispError

class LambdaProcedure(Procedure):
    """A procedure defined by a lambda expression or a define form."""

    def __init__(self, formals, body, env):
        """A procedure with formal parameter list FORMALS (a lisp list),
        whose body is the lisp list BODY, and whose parent environment
        starts with Frame ENV."""
        self.formals = formals
        self.body = body
        self.env = env

    def make_call_frame(self, args, env):
        """Make a frame that binds my formal parameters to ARGS, a lisp list
        of values, for a lexically-scoped call evaluated in environment ENV."""
       
        new_env = self.env.make_child_frame(self.formals, args)
        return new_env

    def __str__(self):
        return str(Pair('lambda', Pair(self.formals, self.body)))

    def __repr__(self):
        return 'LambdaProcedure({0}, {1}, {2})'.format(
            repr(self.formals), repr(self.body), repr(self.env))

class MacroProcedure(LambdaProcedure):
    """A macro: a special form that operates on its unevaluated operands to
    create an expression that is evaluated in place of a call."""

    def apply_macro(self, operands, env):
        """Apply this macro to the operand expressions."""
        return complete_apply(self, operands, env)

def add_builtins(frame, funcs_and_names):
    """Enter bindings in FUNCS_AND_NAMES into FRAME, an environment frame,
    as built-in procedures. Each item in FUNCS_AND_NAMES has the form
    (NAME, PYTHON-FUNCTION, INTERNAL-NAME)."""
    for name, fn, proc_name in funcs_and_names:
        frame.define(name, BuiltinProcedure(fn, name=proc_name))

# Special Forms 

# Each of the following do_xxx_form functions takes the cdr of a special form as
# its first argument---a lisp list representing a special form without the
# initial identifying symbol (if, lambda, quote, ...). Its second argument is
# the environment in which the form is to be evaluated.

def do_define_form(expressions, env):
    """Evaluate a define form."""
    check_form(expressions, 2)
    target = expressions.first
    if lisp_symbolp(target):
        check_form(expressions, 2, 2)
        
        Frame.define(env, expressions.first, lisp_eval(expressions.second.first, env))
        return expressions.first
    elif isinstance(target, Pair) and lisp_symbolp(target.first):
       

        lambd_a =do_lambda_form(Pair(target.second, expressions.second), env)
        Frame.define(env, target.first, lambd_a)
        return target.first
    else:
        bad_target = target.first if isinstance(target, Pair) else target
        raise lispError('non-symbol: {0}'.format(bad_target))

def do_quote_form(expressions, env):
    """Evaluate a quote form."""
    check_form(expressions, 1, 1)
    
    return expressions.first

def do_begin_form(expressions, env):
    """Evaluate a begin form."""
    check_form(expressions, 1)
    return eval_all(expressions, env)

def do_lambda_form(expressions, env):
    """Evaluate a lambda form."""
    check_form(expressions, 2)
    formals = expressions.first
    check_formals(formals)
    
    return LambdaProcedure(formals, expressions.second, env)

def do_if_form(expressions, env):
    """Evaluate an if form."""
    check_form(expressions, 2, 3)
    if lisp_truep(lisp_eval(expressions.first, env)):
        return lisp_eval(expressions.second.first, env, True)
    elif len(expressions) == 3:
        return lisp_eval(expressions.second.second.first, env, True)

def do_and_form(expressions, env):
    """Evaluate a (short-circuited) and form."""
    
    if len(expressions) == 0:    # nil pair
        return True
    
    if len(expressions) == 1:     # If last Pair
        evaled = lisp_eval(expressions.first, env, True)    
    else:
        evaled = lisp_eval(expressions.first, env)
    if lisp_falsep(evaled):
        return evaled
    
    if len(expressions) == 1:
        return evaled
    else:
        return do_and_form(expressions.second, env)

def do_or_form(expressions, env):
    """Evaluate a (short-circuited) or form."""
    
    if len(expressions) ==0:
        return False

    if len(expressions) == 1:     # If last Pair
        evaled = lisp_eval(expressions.first, env, True)    
    else:
        evaled = lisp_eval(expressions.first, env)
    if lisp_truep(evaled):
        return evaled
    
    if len(expressions) == 1:
        return evaled
    else:
        return do_or_form(expressions.second, env)

def do_cond_form(expressions, env):
    """Evaluate a cond form."""
    while expressions is not nil:
        clause = expressions.first
        check_form(clause, 1)
        if clause.first == 'else':
            test = True
            if expressions.second != nil:
                raise lispError('else must be last')
        else:
            test = lisp_eval(clause.first, env)
        if lisp_truep(test):
         
            if len(expressions.first) == 1:
                return test

            return eval_all(expressions.first.second, env)
            
        expressions = expressions.second

def do_let_form(expressions, env):
    """Evaluate a let form."""
    check_form(expressions, 2)
    let_env = make_let_frame(expressions.first, env)
    return eval_all(expressions.second, let_env)

def make_let_frame(bindings, env):
    """Create a child frame of ENV that contains the definitions given in
    BINDINGS. The lisp list BINDINGS must have the form of a proper bindings
    list in a let expression: each item must be a list containing a symbol
    and a lisp expression."""
    if not lisp_listp(bindings):
        raise lispError('bad bindings list in let form')    
    formal, val = nil, nil
    for i in range(len(bindings)):
        check_form(bindings.first, 2, 2)
        formal = Pair(bindings.first.first, formal)
        val = Pair(lisp_eval(bindings.first.second.first, env), val)
        bindings =bindings.second
    check_formals(formal)

    new_env = env.make_child_frame(formal, val)
    return new_env

def do_define_macro(expressions, env):
    """Evaluate a define-macro form."""
    check_form(expressions, 2)
    target = expressions.first
    if isinstance(target, Pair) and lisp_symbolp(target.first):
        body = expressions.second
        formals = target.second

        check_formals(formals)
        macro = MacroProcedure(formals, body, env)
        Frame.define(env, target.first, macro)
        print('DEBUG:', 'IS A MACRO?', isinstance(env.bindings[target.first], MacroProcedure))
        return target.first
    else:
         raise lispError


def do_quasiquote_form(expressions, env):
    """Evaluate a quasiquote form with parameters EXPRESSIONS in
    environment ENV."""
    def quasiquote_item(val, env, level):
        """Evaluate lisp expression VAL that is nested at depth LEVEL in
        a quasiquote form in environment ENV."""
        if not lisp_pairp(val):
            return val
        if val.first == 'unquote':
            level -= 1
            if level == 0:
                expressions = val.second
                check_form(expressions, 1, 1)
                return lisp_eval(expressions.first, env)
        elif val.first == 'quasiquote':
            level += 1
        first = quasiquote_item(val.first, env, level)
        second = quasiquote_item(val.second, env, level)
        return Pair(first, second)

    check_form(expressions, 1, 1)
    return quasiquote_item(expressions.first, env, 1)

def do_unquote(expressions, env):
    raise lispError('unquote outside of quasiquote')


SPECIAL_FORMS = {
    'and': do_and_form,
    'begin': do_begin_form,
    'cond': do_cond_form,
    'define': do_define_form,
    'if': do_if_form,
    'lambda': do_lambda_form,
    'let': do_let_form,
    'or': do_or_form,
    'quote': do_quote_form,
    'define-macro': do_define_macro,
    'quasiquote': do_quasiquote_form,
    'unquote': do_unquote,
}

# Utility methods for checking the structure of lisp programs
def check_form(expr, min, max=float('inf')):
    """Check EXPR is a proper list whose length is at least MIN and no more
    than MAX (default: no maximum). Raises a lispError if this is not the
    case.

    >>> check_form(read_line('(a b)'), 2)
    """
    if not lisp_listp(expr):
        raise lispError('badly formed expression: ' + repl_str(expr))
    length = len(expr)
    if length < min:
        raise lispError('too few operands in form')
    elif length > max:
        raise lispError('too many operands in form')

def check_formals(formals):
    """Check that FORMALS is a valid parameter list, a lisp list of symbols
    in which each symbol is distinct. Raise a lispError if the list of
    formals is not a list of symbols or if any symbol is repeated.

    >>> check_formals(read_line('(a b c)'))
    """
    symbols = set()
    def check_and_add(symbol, is_last):
        if not lisp_symbolp(symbol):
            raise lispError('non-symbol: {0}'.format(symbol))
        if symbol in symbols:
            raise lispError('duplicate symbol: {0}'.format(symbol))
        symbols.add(symbol)

    while isinstance(formals, Pair):
        check_and_add(formals.first, formals.second is nil)
        formals = formals.second


def check_procedure(procedure):
    """Check that PROCEDURE is a valid lisp procedure."""
    if not lisp_procedurep(procedure):
        raise lispError('{0} is not callable: {1}'.format(
            type(procedure).__name__.lower(), repl_str(procedure)))


# Dynamic Scope 
class MuProcedure(Procedure):
    """A procedure defined by a mu expression, which has dynamic scope.
     _________________
    < lisp is cool! >
     -----------------
            \   ^__^
             \  (oo)\_______
                (__)\       )\/\
                    ||----w |
                    ||     ||
    """

    def __init__(self, formals, body):
        """A procedure with formal parameter list FORMALS (a lisp list) and
        lisp list BODY as its definition."""
        self.formals = formals
        self.body = body
    
    def make_call_frame(self, args, env):
        return Frame.make_child_frame(env, self.formals, args)
    def __str__(self):
        return str(Pair('mu', Pair(self.formals, self.body)))

    def __repr__(self):
        return 'MuProcedure({0}, {1})'.format(
            repr(self.formals), repr(self.body))

def do_mu_form(expressions, env):
    """Evaluate a mu form."""
    check_form(expressions, 2)
    formals = expressions.first
    check_formals(formals)    
    return MuProcedure(formals, expressions.second)

SPECIAL_FORMS['mu'] = do_mu_form


# Streams 
class Promise(object):
    """A promise."""
    def __init__(self, expression, env):
        self.expression = expression
        self.env = env

    def evaluate(self):
        if self.expression is not None:
            value = lisp_eval(self.expression, self.env)
            if not (value is nil or isinstance(value, Pair)):
                raise lispError("result of forcing a promise should be a pair or nil, but was %s" % value)
            self.value = value
            self.expression = None
        return self.value

    def __str__(self):
        return '#[promise ({0}forced)]'.format(
                'not ' if self.expression is not None else '')

def do_delay_form(expressions, env):
    """Evaluates a delay form."""
    check_form(expressions, 1, 1)
    return Promise(expressions.first, env)

def do_cons_stream_form(expressions, env):
    """Evaluate a cons-stream form."""
    check_form(expressions, 2, 2)
    return Pair(lisp_eval(expressions.first, env),
                do_delay_form(expressions.second, env))

SPECIAL_FORMS['cons-stream'] = do_cons_stream_form
SPECIAL_FORMS['delay'] = do_delay_form

# Tail Recursion 
class Thunk(object):
    """An expression EXPR to be evaluated in environment ENV."""
    def __init__(self, expr, env):
        self.expr = expr
        self.env = env

def complete_apply(procedure, args, env):
    """Apply procedure to args in env; ensure the result is not a Thunk."""
    val = lisp_apply(procedure, args, env)
    if isinstance(val, Thunk):
        return lisp_eval(val.expr, val.env)
    else:
        return val

def optimize_tail_calls(original_lisp_eval):
    """Return a properly tail recursive version of an eval function."""
    def optimized_eval(expr, env, tail=False):
        """Evaluate lisp expression EXPR in environment ENV. If TAIL,
        return a Thunk containing an expression for further evaluation.
        """
        if tail and not lisp_symbolp(expr) and not self_evaluating(expr):
            return Thunk(expr, env)
        
        result = Thunk(expr, env)

        while isinstance(result, Thunk):
            result = original_lisp_eval(result.expr, result.env)
        return result
    return optimized_eval



# Uncomment the following line to apply tail call optimization 
lisp_eval = optimize_tail_calls(lisp_eval)


# Extra Procedures 
def lisp_map(fn, s, env):
    check_type(fn, lisp_procedurep, 0, 'map')
    check_type(s, lisp_listp, 1, 'map')
    return s.map(lambda x: complete_apply(fn, Pair(x, nil), env))

def lisp_filter(fn, s, env):
    check_type(fn, lisp_procedurep, 0, 'filter')
    check_type(s, lisp_listp, 1, 'filter')
    head, current = nil, nil
    while s is not nil:
        item, s = s.first, s.second
        if complete_apply(fn, Pair(item, nil), env):
            if head is nil:
                head = Pair(item, nil)
                current = head
            else:
                current.second = Pair(item, nil)
                current = current.second
    return head

def lisp_reduce(fn, s, env):
    check_type(fn, lisp_procedurep, 0, 'reduce')
    check_type(s, lambda x: x is not nil, 1, 'reduce')
    check_type(s, lisp_listp, 1, 'reduce')
    value, s = s.first, s.second
    while s is not nil:
        value = complete_apply(fn, lisp_list(value, s.first), env)
        s = s.second
    return value


# Input/Output 
def read_eval_print_loop(next_line, env, interactive=False, quiet=False,
                         startup=False, load_files=(), report_errors=False):
    """Read and evaluate input until an end of file or keyboard interrupt."""
    if startup:
        for filename in load_files:
            lisp_load(filename, True, env)
    while True:
        try:
            src = next_line()
            while src.more_on_line:
                expression = lisp_read(src)
                result = lisp_eval(expression, env)
                if not quiet and result is not None:
                    print(repl_str(result))
        except (lispError, SyntaxError, ValueError, RuntimeError) as err:
            if report_errors:
                if isinstance(err, SyntaxError):
                    err = lispError(err)
                    raise err
            if (isinstance(err, RuntimeError) and
                'maximum recursion depth exceeded' not in getattr(err, 'args')[0]):
                raise
            elif isinstance(err, RuntimeError):
                print('Error: maximum recursion depth exceeded')
            else:
                print('Error:', err)
        except KeyboardInterrupt:  # <Control>-C
            if not startup:
                raise
            print()
            print('KeyboardInterrupt')
            if not interactive:
                return
        except EOFError:  # <Control>-D, etc.
            print()
            return

def lisp_load(*args):
    """Load a lisp source file. ARGS should be of the form (SYM, ENV) or
    (SYM, QUIET, ENV). The file named SYM is loaded into environment ENV,
    with verbosity determined by QUIET (default true)."""
    if not (2 <= len(args) <= 3):
        expressions = args[:-1]
        raise lispError('"load" given incorrect number of arguments: '
                          '{0}'.format(len(expressions)))
    sym = args[0]
    quiet = args[1] if len(args) > 2 else True
    env = args[-1]
    if (lisp_stringp(sym)):
        sym = eval(sym)
    check_type(sym, lisp_symbolp, 0, 'load')
    with lisp_open(sym) as infile:
        lines = infile.readlines()
    args = (lines, None) if quiet else (lines,)
    def next_line():
        return buffer_lines(*args)

    read_eval_print_loop(next_line, env, quiet=quiet, report_errors=True)

def lisp_open(filename):
    """If either FILENAME or FILENAME.scm is the name of a valid file,
    return a Python file opened to it. Otherwise, raise an error."""
    try:
        return open(filename)
    except IOError as exc:
        if filename.endswith('.scm'):
            raise lispError(str(exc))
    try:
        return open(filename + '.scm')
    except IOError as exc:
        raise lispError(str(exc))

def create_global_frame():
    """Initialize and return a single-frame environment with built-in names."""
    env = Frame(None)
    env.define('eval',
               BuiltinProcedure(lisp_eval, True, 'eval'))
    env.define('apply',
               BuiltinProcedure(complete_apply, True, 'apply'))
    env.define('load',
               BuiltinProcedure(lisp_load, True, 'load'))
    env.define('procedure?',
               BuiltinProcedure(lisp_procedurep, False, 'procedure?'))
    env.define('map',
               BuiltinProcedure(lisp_map, True, 'map'))
    env.define('filter',
               BuiltinProcedure(lisp_filter, True, 'filter'))
    env.define('reduce',
               BuiltinProcedure(lisp_reduce, True, 'reduce'))
    env.define('undefined', None)
    add_builtins(env, BUILTINS)
    return env

@main
def run(*argv):
    import argparse
    parser = argparse.ArgumentParser(description='CS 61A lisp Interpreter')
    parser.add_argument('-load', '-i', action='store_true',
                       help='run file interactively')
    parser.add_argument('file', nargs='?',
                        type=argparse.FileType('r'), default=None,
                        help='lisp file to run')
    args = parser.parse_args()


    next_line = buffer_input
    interactive = True
    load_files = []

    if args.file is not None:
        if args.load:
            load_files.append(getattr(args.file, 'name'))
        else:
            lines = args.file.readlines()
            def next_line():
                return buffer_lines(lines)
            interactive = False

    read_eval_print_loop(next_line, create_global_frame(), startup=True,
                         interactive=interactive, load_files=load_files)
    tlisp_exitonclick()