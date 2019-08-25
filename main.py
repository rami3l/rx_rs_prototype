import math
import sys
import operator as op
from copy import copy as cp
from copy import deepcopy as dcp

# Types

"""
Todo: implement append
class List(object):

    def __init__(self):
        self = None

    @classmethod
    def from_list(cls, list_):
        res = cls()
        if list_:
            res.head = car(list_)
            res.tail = cls.from_list(cdr(list_))
        return res

    def __getitem__(self, index):
        if index == 0:
            return car(self)
        elif index > 0:
            return self.tail.__getitem__(index-1)
        elif index == -1:
            inner = dcp(self)
            while inner.tail:
                inner = inner.head
            return inner.head
        else:
            raise NotImplementedError

    @classmethod
    def cons(cls, head, tail):
        res = cls()
        res.head = head
        res.tail = tail
        return res
"""


class List(list):
    @classmethod
    def from_list(cls, list_):
        return cls(list_)

    @property
    def head(self):
        return self[0]

    @property
    def tail(self):
        return self[1:]


Symbol = str
Number = (int, float)
Atom = (Symbol, Number)
Exp = (Atom, List)

# Primitive definitions
begin = lambda *x: x[-1]


def car(x):
    if isinstance(x, List):
        return x.head
    else:
        return x[0]


def cdr(x):
    if isinstance(x, List):
        return x.tail
    else:
        return x[1:]


def cons(x, y):
    return [x] + y
    # return List.cons(x, y)
# ! Attention: the function cons here cannot make up a pair,
# ! maybe we should refactor the List type


list_scm = lambda *x: List(x)


def is_list(x): return isinstance(x, List)


def is_null(x): return x == list()


def is_number(x): return isinstance(x, Number)


def print_scm(x): return print(">> {}".format(x))


def is_symbol(x): return isinstance(x, Symbol)


def is_closure(x): return isinstance(x, Closure)

# The environment model
# Env = dict


class Env(dict):
    """
    An environment is a dict {"var": val}.
    """

    def __init__(self, outer=None):
        self.outer = outer

    def find(self, symbol):
        # find the innermost Env where symbol appears
        if symbol in self:
            return self
        else:
            return self.outer.find(symbol)

    def lookup(self, symbol):
        return self.find(symbol)[symbol]


# The closure model
class Closure(object):
    """
    A closure is a structure that captures the lambda body and the local env.
    '(lambda (x) (+ x y)) => ('closure '[(x) (+ x y)] env)
    """

    def __init__(self, body, env):
        self.body = body
        self.env = env

    def __repr__(self):
        return "<Closure: {}>".format(" ".join(self.body[0]))


def apply(func, args: list):
    """
    The apply function in Python.
    """
    return func(*args)


def tokenize(str_exp) -> list:
    return str_exp.replace("(", " ( ").replace(")", " ) ").split()


def atom(token):
    try:
        return int(token)
    except:
        try:
            return float(token)
        except:
            return token


def gen_ast(tokens: list) -> List:
    if not tokens:
        raise SyntaxError("Unexpected EOF")
    head = tokens.pop(0)
    if head == "(":
        # if we have a list ahead of us, we return that list
        res = List()
        try:
            while tokens[0] != ")":
                res.append(gen_ast(tokens))
                # recursion: deal with the tail of the list
                # ! Attention: we are appending sub-expressions (including atoms) to the result
                # Todo: refactor this function
        except IndexError:
            raise SyntaxError("Mismatched parentheses")
        tokens.pop(0)  # pop off ")"
        return res
    elif head == ")":
        raise SyntaxError("Mismatched parentheses")
    else:
        # if the head is a single atom, we return just the head
        return atom(head)


def parse(str_exp: str) -> List:
    return gen_ast(tokenize(str_exp))


# Prelude
def get_prelude():
    res = Env()
    res.update(vars(math))  # sin, cos, sqrt, pi, ...
    res.update({
        '+': op.add,
        '-': op.sub,
        '*': op.mul,
        '/': op.truediv,
        '<': op.lt,
        '<=': op.le,
        '>': op.gt,
        '>=': op.ge,
        '=': op.eq,
        'abs': abs,
        'append': op.add,
        'apply': apply,
        'begin': begin,
        'car': car,
        'cdr': cdr,
        'cons': cons,
        'eq?': op.is_,
        'equal?': op.eq,
        'expt': pow,
        'length': len,
        'list': list_scm,
        'list?': is_list,
        # 'map': list_map,
        # We can define map in pure scheme.
        # * (define map (lambda (f l) (if (null? l) null (cons (f (car l)) (map f (cdr l))))))
        'max': max,
        'min': min,
        'not': op.not_,
        'null?': is_null,
        'number?': is_number,
        'print': print_scm,
        'procedure?': is_closure,
        'round': round,
        'symbol?': is_symbol,
        '#t': True,
        '#f': False,
        'null': List(),
    })
    return res


global_env = get_prelude()


def eval(exp: Exp, env=global_env):
    if isinstance(exp, Number):
        return exp
    elif isinstance(exp, Symbol):
        # return env[exp]
        try:
            return env.lookup(exp)
        except AttributeError:
            raise RuntimeError('Symbol "{}" undefined'.format(exp))
    elif isinstance(exp, List):
        head, *tail = exp
        # print("head: {}\ntail:{}".format(head,tail))
        if head == "quote":
            return tail[0]
            # ! multi-quote unimplemented
        elif head == "lambda":
            closure_env = Env(outer=env)
            return Closure(tail, closure_env)
        elif head == "define":
            # updates the current environment
            symbol, definition = tail
            env[symbol] = eval(definition, env)
            print('>> Symbol "{}" defined as {}'.format(symbol, env[symbol]))
        elif head == "if":
            condition, then_, else_ = tail
            return eval(then_ if eval(condition, env) else else_, env)
        elif head == "cond":
            for condition, then_ in tail:
                if condition == "else" or eval(condition, env):
                    return eval(then_, env)
                else:
                    raise SyntaxError("Missing else clause")
        elif head == "set!":
            symbol, definition = tail
            try:
                env.find(symbol)[symbol] = eval(definition, env)
            except AttributeError:
                env[symbol] = eval(definition, env)
            print('>> Symbol "{}" set to {}'.format(symbol, env[symbol]))
        else:
            # return env[head](*(eval(i,env) for i in tail))
            return apply_scm(eval(head, env), (eval(i, env) for i in tail))
    else:
        raise RuntimeError("eval: expected Exp, not {}".format(type(exp)))


def apply_scm(proc, args: list):
    """
    The apply function in Scheme.
    """
    # print("apply_scm:")
    prelude = get_prelude()
    if proc in prelude.values():
        # print("Going thru prelude")
        return apply(proc, args)
    elif isinstance(proc, Closure):
        # print("Going thru closure")
        # '(lambda (x) (+ x y)) => ('closure '[(x) (+ x y)] env)
        body = proc.body
        local_env = cp(proc.env)
        local_env.update({i: arg for i, arg in zip(body[0], args)})
        return eval(body[1], local_env)
    else:
        raise RuntimeError("Apply_scm Error")


def repl():
    """
    A prompt-read-eval-print loop.
    """
    count = 0
    print("<rx.rs prototype>")
    while True:
        count += 1
        print("#;{}> ".format(count), end="")
        str_exp = input()
        if str_exp == ",q":
            print("Quitting...")
            break
        try:
            val = eval(parse(str_exp), global_env)
            if val:
                print("=> {}".format(scm_str(val)))
        except (RuntimeError, SyntaxError) as e:
            print("Error: {}".format(e))
            continue


def scm_str(exp):
    """
    Convert a Python object back into a Scheme-readable string.
    """
    if isinstance(exp, list):
        return '(' + ' '.join(map(scm_str, exp)) + ')'
    else:
        return str(exp)


def main():
    args = sys.argv
    if len(args) == 1:
        repl()
    else:
        # Todo: interpret an external .scm file
        pass


if __name__ == "__main__":
    main()
