"""This module implements the built-in procedures of the lisp language."""

from __future__ import print_function  # Python 2 compatibility

import math
import numbers
import operator
import sys
from lisp_reader import Pair, nil, repl_str
import lisp_interpreter

try:
    import turtle
    import tkinter
except:
    print("warning: could not import the turtle module.", file=srys.stderr)

class lispError(Exception):
    """Exception indicating an error in a lisp program."""

# Built-In Procedures
# A list of triples (NAME, PYTHON-FUNCTION, INTERNAL-NAME).  Added to by
# builtin and used in lisp.create_global_frame.
BUILTINS = []

def builtin(*names):
    """An annotation to convert a Python function into a BuiltinProcedure."""
    def add(fn):
        for name in names:
            BUILTINS.append((name, fn, names[0]))
        return fn
    return add

def check_type(val, predicate, k, name):
    """Returns VAL.  Raises a lispError if not PREDICATE(VAL)
    using "argument K of NAME" to describe the offending value."""
    if not predicate(val):
        msg = "argument {0} of {1} has wrong type ({2})"
        raise lispError(msg.format(k, name, type(val).__name__))
    return val

@builtin("boolean?")
def lisp_booleanp(x):
    return x is True or x is False

def lisp_truep(val):
    """All values in lisp are true except False."""
    return val is not False

def lisp_falsep(val):
    """Only False is false in lisp."""
    return val is False

@builtin("not")
def lisp_not(x):
    return not lisp_truep(x)

@builtin("equal?")
def lisp_equalp(x, y):
    if lisp_pairp(x) and lisp_pairp(y):
        return lisp_equalp(x.first, y.first) and lisp_equalp(x.second, y.second)
    elif lisp_numberp(x) and lisp_numberp(y):
        return x == y
    else:
        return type(x) == type(y) and x == y

@builtin("eq?")
def lisp_eqp(x, y):
    if lisp_numberp(x) and lisp_numberp(y):
        return x == y
    elif lisp_symbolp(x) and lisp_symbolp(y):
        return x == y
    else:
        return x is y

@builtin("pair?")
def lisp_pairp(x):
    return isinstance(x, Pair)

@builtin("lisp-valid-cdr?")
def lisp_valid_cdrp(x):
    return lisp_pairp(x) or lisp_nullp(x) or lisp_promisep(x)

# Streams
@builtin("promise?")
def lisp_promisep(x):
    return type(x).__name__ == 'Promise'

@builtin("force")
def lisp_force(x):
    check_type(x, lisp_promisep, 0, 'promise')
    return x.evaluate()

@builtin("cdr-stream")
def lisp_cdr_stream(x):
    check_type(x, lambda x: lisp_pairp(x) and lisp_promisep(x.second), 0, 'cdr-stream')
    return lisp_force(x.second)

@builtin("null?")
def lisp_nullp(x):
    return x is nil

@builtin("list?")
def lisp_listp(x):
    """Return whether x is a well-formed list. Assumes no cycles."""
    while x is not nil:
        if not isinstance(x, Pair):
            return False
        x = x.second
    return True

@builtin("length")
def lisp_length(x):
    check_type(x, lisp_listp, 0, 'length')
    if x is nil:
        return 0
    return len(x)

@builtin("cons")
def lisp_cons(x, y):
    return Pair(x, y)

@builtin("car")
def lisp_car(x):
    check_type(x, lisp_pairp, 0, 'car')
    return x.first

@builtin("cdr")
def lisp_cdr(x):
    check_type(x, lisp_pairp, 0, 'cdr')
    return x.second

# Mutation extras
@builtin("set-car!")
def lisp_car(x, y):
    check_type(x, lisp_pairp, 0, 'set-car!')
    x.first = y

@builtin("set-cdr!")
def lisp_cdr(x, y):
    check_type(x, lisp_pairp, 0, 'set-cdr!')
    check_type(y, lisp_valid_cdrp, 1, 'set-cdr!')
    x.second = y

@builtin("list")
def lisp_list(*vals):
    result = nil
    for e in reversed(vals):
        result = Pair(e, result)
    return result

@builtin("append")
def lisp_append(*vals):
    if len(vals) == 0:
        return nil
    result = vals[-1]
    for i in range(len(vals)-2, -1, -1):
        v = vals[i]
        if v is not nil:
            check_type(v, lisp_pairp, i, 'append')
            r = p = Pair(v.first, result)
            v = v.second
            while lisp_pairp(v):
                p.second = Pair(v.first, result)
                p = p.second
                v = v.second
            result = r
    return result

@builtin("string?")
def lisp_stringp(x):
    return isinstance(x, str) and x.startswith('"')

@builtin("symbol?")
def lisp_symbolp(x):
    return isinstance(x, str) and not lisp_stringp(x)


@builtin("number?")
def lisp_numberp(x):
    return isinstance(x, numbers.Real) and not lisp_booleanp(x)

@builtin("integer?")
def lisp_integerp(x):
    return lisp_numberp(x) and (isinstance(x, numbers.Integral) or int(x) == x)

def _check_nums(*vals):
    """Check that all arguments in VALS are numbers."""
    for i, v in enumerate(vals):
        if not lisp_numberp(v):
            msg = "operand {0} ({1}) is not a number"
            raise lispError(msg.format(i, v))

def _arith(fn, init, vals):
    """Perform the FN operation on the number values of VALS, with INIT as
    the value when VALS is empty. Returns the result as a lisp value."""
    _check_nums(*vals)
    s = init
    for val in vals:
        s = fn(s, val)
    if int(s) == s:
        s = int(s)
    return s

@builtin("+")
def lisp_add(*vals):
    return _arith(operator.add, 0, vals)

@builtin("-")
def lisp_sub(val0, *vals):
    _check_nums(val0, *vals) # fixes off-by-one error
    if len(vals) == 0:
        return -val0
    return _arith(operator.sub, val0, vals)

@builtin("*")
def lisp_mul(*vals):
    return _arith(operator.mul, 1, vals)

@builtin("/")
def lisp_div(val0, *vals):
    _check_nums(val0, *vals) # fixes off-by-one error
    try:
        if len(vals) == 0:
            return operator.truediv(1, val0)
        return _arith(operator.truediv, val0, vals)
    except ZeroDivisionError as err:
        raise lispError(err)

@builtin("expt")
def lisp_expt(val0, val1):
    _check_nums(val0, val1)
    return pow(val0, val1)

@builtin("abs")
def lisp_abs(val0):
    return abs(val0)

@builtin("quotient")
def lisp_quo(val0, val1):
    _check_nums(val0, val1)
    try:
        return -(-val0 // val1) if (val0 < 0) ^ (val1 < 0) else val0 // val1
    except ZeroDivisionError as err:
        raise lispError(err)

@builtin("modulo")
def lisp_modulo(val0, val1):
    _check_nums(val0, val1)
    try:
        return val0 % val1
    except ZeroDivisionError as err:
        raise lispError(err)

@builtin("remainder")
def lisp_remainder(val0, val1):
    _check_nums(val0, val1)
    try:
        result = val0 % val1
    except ZeroDivisionError as err:
        raise lispError(err)
    while result < 0 and val0 > 0 or result > 0 and val0 < 0:
        result -= val1
    return result

def number_fn(module, name, fallback=None):
    """A lisp built-in procedure that calls the numeric Python function named
    MODULE.FN."""
    py_fn = getattr(module, name) if fallback is None else getattr(module, name, fallback)
    def lisp_fn(*vals):
        _check_nums(*vals)
        return py_fn(*vals)
    return lisp_fn

# Add number functions in the math module as built-in procedures in lisp
for _name in ["acos", "acosh", "asin", "asinh", "atan", "atan2", "atanh",
              "ceil", "copysign", "cos", "cosh", "degrees", "floor", "log",
              "log10", "log1p", "radians", "sin", "sinh", "sqrt",
              "tan", "tanh", "trunc"]:
    builtin(_name)(number_fn(math, _name))
builtin("log2")(number_fn(math, "log2", lambda x: math.log(x, 2)))  # Python 2 compatibility

def _numcomp(op, x, y):
    _check_nums(x, y)
    return op(x, y)

@builtin("=")
def lisp_eq(x, y):
    return _numcomp(operator.eq, x, y)

@builtin("<")
def lisp_lt(x, y):
    return _numcomp(operator.lt, x, y)

@builtin(">")
def lisp_gt(x, y):
    return _numcomp(operator.gt, x, y)

@builtin("<=")
def lisp_le(x, y):
    return _numcomp(operator.le, x, y)

@builtin(">=")
def lisp_ge(x, y):
    return _numcomp(operator.ge, x, y)

@builtin("even?")
def lisp_evenp(x):
    _check_nums(x)
    return x % 2 == 0

@builtin("odd?")
def lisp_oddp(x):
    _check_nums(x)
    return x % 2 == 1

@builtin("zero?")
def lisp_zerop(x):
    _check_nums(x)
    return x == 0

##
## Other operations
##

@builtin("atom?")
def lisp_atomp(x):
    return (lisp_booleanp(x) or lisp_numberp(x) or lisp_symbolp(x) or
            lisp_nullp(x) or lisp_stringp(x))

@builtin("display")
def lisp_display(val):
    if lisp_stringp(val):
        val = eval(val)
    print(repl_str(val), end="")

@builtin("print")
def lisp_print(val):
    print(repl_str(val))

@builtin("newline")
def lisp_newline():
    print()
    sys.stdout.flush()

@builtin("error")
def lisp_error(msg=None):
    msg = "" if msg is None else repl_str(msg)
    raise lispError(msg)

@builtin("exit")
def lisp_exit():
    raise EOFError

#Only for use in lisp project
@builtin("print-then-return")
def lisp_print_return(val1, val2):
    print(repl_str(val1))
    return val2



##
## Turtle graphics (non-standard)
##

_turtle_screen_on = False

def turtle_screen_on():
    return _turtle_screen_on

def _tlisp_prep():
    global _turtle_screen_on
    if not _turtle_screen_on:
        _turtle_screen_on = True
        turtle.title("lisp Turtles")
        turtle.mode('logo')

@builtin("forward", "fd")
def tlisp_forward(n):
    """Move the turtle forward a distance N units on the current heading."""
    _check_nums(n)
    _tlisp_prep()
    turtle.forward(n)

@builtin("backward", "back", "bk")
def tlisp_backward(n):
    """Move the turtle backward a distance N units on the current heading,
    without changing direction."""
    _check_nums(n)
    _tlisp_prep()
    turtle.backward(n)

@builtin("left", "lt")
def tlisp_left(n):
    """Rotate the turtle's heading N degrees counterclockwise."""
    _check_nums(n)
    _tlisp_prep()
    turtle.left(n)

@builtin("right", "rt")
def tlisp_right(n):
    """Rotate the turtle's heading N degrees clockwise."""
    _check_nums(n)
    _tlisp_prep()
    turtle.right(n)

@builtin("circle")
def tlisp_circle(r, extent=None):
    """Draw a circle with center R units to the left of the turtle (i.e.,
    right if N is negative.  If EXTENT is not None, then draw EXTENT degrees
    of the circle only.  Draws in the clockwise direction if R is negative,
    and otherwise counterclockwise, leaving the turtle facing along the
    arc at its end."""
    if extent is None:
        _check_nums(r)
    else:
        _check_nums(r, extent)
    _tlisp_prep()
    turtle.circle(r, extent and extent)

@builtin("setposition", "setpos", "goto")
def tlisp_setposition(x, y):
    """Set turtle's position to (X,Y), heading unchanged."""
    _check_nums(x, y)
    _tlisp_prep()
    turtle.setposition(x, y)

@builtin("setheading", "seth")
def tlisp_setheading(h):
    """Set the turtle's heading H degrees clockwise from north (up)."""
    _check_nums(h)
    _tlisp_prep()
    turtle.setheading(h)

@builtin("penup", "pu")
def tlisp_penup():
    """Raise the pen, so that the turtle does not draw."""
    _tlisp_prep()
    turtle.penup()

@builtin("pendown", "pd")
def tlisp_pendown():
    """Lower the pen, so that the turtle starts drawing."""
    _tlisp_prep()
    turtle.pendown()

@builtin("showturtle", "st")
def tlisp_showturtle():
    """Make turtle visible."""
    _tlisp_prep()
    turtle.showturtle()

@builtin("hideturtle", "ht")
def tlisp_hideturtle():
    """Make turtle visible."""
    _tlisp_prep()
    turtle.hideturtle()

@builtin("clear")
def tlisp_clear():
    """Clear the drawing, leaving the turtle unchanged."""
    _tlisp_prep()
    turtle.clear()

@builtin("color")
def tlisp_color(c):
    """Set the color to C, a string such as '"red"' or '"#ffc0c0"' (representing
    hexadecimal red, green, and blue values."""
    _tlisp_prep()
    check_type(c, lisp_stringp, 0, "color")
    turtle.color(eval(c))

@builtin("rgb")
def tlisp_rgb(red, green, blue):
    """Return a color from RED, GREEN, and BLUE values from 0 to 1."""
    colors = (red, green, blue)
    for x in colors:
        if x < 0 or x > 1:
            raise lispError("Illegal color intensity in " + repl_str(colors))
    scaled = tuple(int(x*255) for x in colors)
    return '"#%02x%02x%02x"' % scaled

@builtin("begin_fill")
def tlisp_begin_fill():
    """Start a sequence of moves that outline a shape to be filled."""
    _tlisp_prep()
    turtle.begin_fill()

@builtin("end_fill")
def tlisp_end_fill():
    """Fill in shape drawn since last begin_fill."""
    _tlisp_prep()
    turtle.end_fill()

@builtin("bgcolor")
def tlisp_bgcolor(c):
    _tlisp_prep()
    check_type(c, lisp_stringp, 0, "bgcolor")
    turtle.bgcolor(eval(c))

@builtin("exitonclick")
def tlisp_exitonclick():
    """Wait for a click on the turtle window, and then close it."""
    global _turtle_screen_on
    if _turtle_screen_on:
        print("Close or click on turtle window to complete exit")
        turtle.exitonclick()
        _turtle_screen_on = False

@builtin("speed")
def tlisp_speed(s):
    """Set the turtle's animation speed as indicated by S (an integer in
    0-10, with 0 indicating no animation (lines draw instantly), and 1-10
    indicating faster and faster movement."""
    check_type(s, lisp_integerp, 0, "speed")
    _tlisp_prep()
    turtle.speed(s)

@builtin("pixel")
def tlisp_pixel(x, y, c):
    """Draw a filled box of pixels (default 1 pixel) at (X, Y) in color C."""
    check_type(c, lisp_stringp, 0, "pixel")
    color = eval(c)
    canvas = turtle.getcanvas()
    w, h = canvas.winfo_width(), canvas.winfo_height()
    if not hasattr(tlisp_pixel, 'image'):
        _tlisp_prep()
        tlisp_pixel.image = tkinter.PhotoImage(width=w, height=h)
        canvas.create_image((0, 0), image=tlisp_pixel.image, state="normal")
    size = tlisp_pixel.size
    for dx in range(size):
        for dy in range(size):
            screenx, screeny = x * size + dx, h-(y * size + dy)
            if 0 < screenx < w and 0 < screeny < h:
                tlisp_pixel.image.put(color, (screenx, screeny))

tlisp_pixel.size = 1
@builtin("pixelsize")
def tlisp_pixelsize(size):
    """Change pixel size to SIZE."""
    _check_nums(size)
    if size <= 0 or not isinstance(size, numbers.Integral):
        raise lispError("Invalid pixel size: " + repl_str(size))
    tlisp_pixel.size = size

@builtin("screen_width")
def tlisp_screen_width():
    """Screen width in pixels of the current size (default 1)."""
    return turtle.getcanvas().winfo_width() // tlisp_pixel.size

@builtin("screen_height")
def tlisp_screen_height():
    """Screen height in pixels of the current size (default 1)."""
    return turtle.getcanvas().winfo_height() // tlisp_pixel.size