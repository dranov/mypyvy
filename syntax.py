from __future__ import annotations

from contextlib import contextmanager
import itertools
import logging
import ply, ply.lex, ply.yacc
import sys
from typing import List, Union, Tuple, Optional, Dict, Iterator, \
    Callable, Any, NoReturn, Set, TypeVar, Generic, Iterable
from typing_extensions import Protocol
import z3



Token = ply.lex.LexToken

def error(tok: Optional[Token], msg: str) -> NoReturn:
    raise Exception('%s: %s' %
                    ('%s:%s:%s' % (tok.filename, tok.lineno, tok.col)
                     if tok is not None else 'None', msg))

B = TypeVar('B')

class Sort(object):
    def __repr__(self) -> str:
        raise Exception('Unexpected sort %s does not implement __repr__ method' % type(self))

    def __str__(self) -> str:
        raise Exception('Unexpected sort %s does not implement __str__ method' % repr(self))

    def resolve(self, scope: Scope[B]) -> None:
        raise Exception('Unexpected sort %s does not implement resolve method' % repr(self))

    def to_z3(self) -> z3.SortRef:
        raise Exception('Unexpected sort %s does not implement to_z3 method' % repr(self))

    def _denote(self) -> object:
        raise Exception('Unexpected sort %s does not implement _denote method' % repr(self))

    def __hash__(self) -> int:
        return hash(self._denote())

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Sort):
            return False
        return self._denote() == other._denote()

    def __ne__(self, other: object) -> bool:
        return not (self == other)


class HasSortField(Protocol):
    sort: InferenceSort

class SortInferencePlaceholder(object):
    def __init__(self, d: Optional[HasSortField]=None) -> None:
        self.backpatches: List[HasSortField] = []
        if d is not None:
            self.add(d)

    def add(self, d: HasSortField) -> None:
        self.backpatches.append(d)

    def solve(self, sort: Sort) -> None:
        for d in self.backpatches:
            d.sort = sort

    def merge(self, other: SortInferencePlaceholder) -> None:
        for d in other.backpatches:
            assert d.sort is other, (repr(d), repr(other))
            d.sort = self
            self.backpatches.append(d)

InferenceSort = Union[Sort, SortInferencePlaceholder, None]


PREC_BOT = 0
PREC_NOT = 1
PREC_EQ = 2
PREC_AND = 3
PREC_OR = 4
PREC_IMPLIES = 5
PREC_IFF = 6
PREC_QUANT = 7
PREC_TOP = 8

PREC_ASSOC = {
    PREC_BOT: 'NONE',
    PREC_NOT: 'NONE',
    PREC_EQ: 'NONE',
    PREC_AND: 'LEFT',
    PREC_OR: 'LEFT',
    PREC_IMPLIES: 'RIGHT',
    PREC_IFF: 'NONE',
    PREC_QUANT: 'NONE',
    PREC_TOP: 'NONE'
}

def no_parens(ip: int, op: int, side: str) -> bool:
    return ip < op or (ip == op and side == PREC_ASSOC[ip])

class Z3Translator(object):
    def __init__(self, scope: Scope[z3.ExprRef], key: Optional[str]=None, key_old: Optional[str]=None) -> None:
        self.scope = scope
        self.key = key
        self.key_old = key_old
        self.expr_cache: Dict[Tuple[Expr, bool], z3.ExprRef] = {}
        self.transition_cache: Dict[TransitionDecl, z3.ExprRef] = {}

    def bind(self, binder: Binder) -> List[z3.ExprRef]:
        bs = []
        for sv in binder.vs:
            n = sv.name
            assert sv.sort is not None and not isinstance(sv.sort, SortInferencePlaceholder)
            bs.append(z3.Const(n, sv.sort.to_z3()))
        return bs

    def translate_expr(self, expr: Expr, old: bool=False) -> z3.ExprRef:
        t = (expr, old)
        if t not in self.expr_cache:
            if isinstance(expr, Bool):
                self.expr_cache[t] = z3.BoolVal(expr.val)
            elif isinstance(expr, UnaryExpr):
                if expr.op == 'OLD':
                    assert not old and self.key_old is not None
                    self.expr_cache[t] = self.translate_expr(expr.arg, old=True)
                else:
                    unop = z3_UNOPS[expr.op]
                    assert unop is not None
                    self.expr_cache[t] = unop(self.translate_expr(expr.arg, old))
            elif isinstance(expr, BinaryExpr):
                binop = z3_BINOPS[expr.op]
                self.expr_cache[t] = binop(self.translate_expr(expr.arg1, old), self.translate_expr(expr.arg2, old))
            elif isinstance(expr, AppExpr):
                if not old:
                    k = self.key
                else:
                    assert self.key_old is not None
                    k = self.key_old
                d = self.scope.get(expr.rel)
                assert d is not None
                assert isinstance(d, RelationDecl)
                R = d.to_z3(k)
                assert isinstance(R, z3.FuncDeclRef)
                self.expr_cache[t] = R(*(self.translate_expr(arg, old) for arg in expr.args))
            elif isinstance(expr, QuantifierExpr):
                bs = self.bind(expr.binder)
                with self.scope.in_scope(list(zip(expr.binder.vs, bs))):
                    e = self.translate_expr(expr.body, old)
                q = z3.ForAll if expr.quant == 'FORALL' else z3.Exists
                self.expr_cache[t] = q(bs, e)
            elif isinstance(expr, Id):
                d = self.scope.get(expr.name)
                assert d is not None
                if isinstance(d, RelationDecl) or \
                   isinstance(d, ConstantDecl):
                    if not old:
                        k = self.key
                    else:
                        assert not d.mutable or self.key_old is not None
                        k = self.key_old
                    x = d.to_z3(k)
                    assert isinstance(x, z3.ExprRef)
                    self.expr_cache[t] = x
                else:
                    _, e = d
                    self.expr_cache[t] = e
            else:
                assert False

        return self.expr_cache[t]

    def frame(self, mods: Iterable[ModifiesClause]) -> List[z3.ExprRef]:
        frame = []
        R: Iterator[Union[RelationDecl, ConstantDecl]] = iter(self.scope.relations.values())
        C: Iterator[Union[RelationDecl, ConstantDecl]] = iter(self.scope.constants.values())
        for d in itertools.chain(R, C):
            if not d.mutable or any(mc.name == d.name for mc in mods):
                continue

            if isinstance(d, ConstantDecl) or len(d.arity) == 0:
                lhs = d.to_z3(self.key)
                rhs = d.to_z3(self.key_old)
                assert isinstance(lhs, z3.ExprRef) and isinstance(rhs, z3.ExprRef)
                e = lhs == rhs
            else:
                cs: List[z3.ExprRef] = []
                i = 0
                for s in d.arity:
                    cs.append(z3.Const('x' + str(i), s.to_z3()))
                    i += 1

                lhs = d.to_z3(self.key)
                rhs = d.to_z3(self.key_old)
                assert isinstance(lhs, z3.FuncDeclRef) and isinstance(rhs, z3.FuncDeclRef)

                e = z3.Forall(cs, lhs(*cs) == rhs(*cs))

            frame.append(e)

        return frame

    def translate_transition(self, t: TransitionDecl) -> z3.ExprRef:
        if t not in self.transition_cache:

            bs = self.bind(t.binder)
            with self.scope.in_scope(list(zip(t.binder.vs, bs))):
                self.transition_cache[t] = \
                    z3.Exists(bs, z3.And(self.translate_expr(t.expr), *self.frame(t.mods)))

        return self.transition_cache[t]



class Expr(object):
    def __repr__(self) -> str:
        raise Exception('Unexpected expr %s does not implement __repr__ method' % type(self))

    def __str__(self) -> str:
        buf: List[str] = []
        self.pretty(buf, PREC_TOP, 'NONE')
        return ''.join(buf)

    def resolve(self, scope: Scope[InferenceSort], sort: InferenceSort) -> InferenceSort:
        raise Exception('Unexpected expression %s does not implement resolve method' %
                        repr(self))

    def _denote(self) -> object:
        raise Exception('Unexpected expr %s does not implement _denote method' % repr(self))

    def __hash__(self) -> int:
        return hash(self._denote())

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Expr):
            return False
        return self._denote() == other._denote()

    def __ne__(self, other: object) -> bool:
        return not (self == other)

    def pretty(self, buf: List[str], prec: int, side: str) -> None:
        needs_parens = not no_parens(self.prec(), prec, side)

        if needs_parens:
            buf.append('(')
            prec = PREC_TOP
            side = 'NONE'

        self._pretty(buf, prec, side)

        if needs_parens:
            buf.append(')')

    def prec(self) -> int:
        raise Exception('Unexpected expr %s does not implement prec method' % repr(self))

    def _pretty(self, buf: List[str], prec: int, side: str) -> None:
        raise Exception('Unexpected expr %s does not implement pretty method' % repr(self))

    def free_ids(self) -> List[str]:
        raise Exception('Unexpected expr %s does not implement contains_var method' %
                        repr(self))

class Bool(Expr):
    def __init__(self, tok: Optional[Token], val: bool) -> None:
        self.tok = tok
        self.val = val

    def __repr__(self) -> str:
        return 'true' if self.val else 'false'

    def _denote(self) -> object:
        return self.val

    def prec(self) -> int:
        return PREC_BOT

    def _pretty(self, buf: List[str], prec: int, side: str) -> None:
        buf.append(str(self.val))

    def resolve(self, scope: Scope[InferenceSort], sort: InferenceSort) -> InferenceSort:
        check_constraint(self.tok, sort, BoolSort)
        return BoolSort

    def free_ids(self) -> List[str]:
        return []

UNOPS = {
    'NOT',
    'OLD'
}
z3_UNOPS: Dict[str, Optional[Callable[[z3.ExprRef], z3.ExprRef]]] = {
    'NOT': z3.Not,
    'OLD': None
}

def check_constraint(tok: Optional[Token], expected: InferenceSort, actual: InferenceSort) -> None:
    if expected is None or actual is None:
        pass
    elif isinstance(expected, Sort):
        if isinstance(actual, Sort):
            if expected != actual:
                error(tok, 'expected sort %s but got %s' % (expected, actual))
        else:
            actual.solve(expected)
    else:
        if isinstance(actual, Sort):
            expected.solve(actual)
        else:
            expected.merge(actual)


class UnaryExpr(Expr):
    def __init__(self, tok: Optional[Token], op: str, arg: Expr) -> None:
        assert op in UNOPS
        self.tok = tok
        self.op = op
        self.arg = arg

    def resolve(self, scope: Scope[InferenceSort], sort: InferenceSort) -> InferenceSort:
        if self.op == 'OLD':
            return self.arg.resolve(scope, sort)
        else:
            assert self.op == 'NOT'
            check_constraint(self.tok, sort, BoolSort)
            self.arg.resolve(scope, BoolSort)
            return BoolSort

    def _denote(self) -> object:
        return (UnaryExpr, self.op, self.arg)

    def __repr__(self) -> str:
        return 'UnaryExpr(%s, %s)' % (self.op, repr(self.arg))

    def prec(self) -> int:
        if self.op == 'NOT':
            return PREC_NOT
        elif self.op == 'OLD':
            return PREC_BOT
        else:
            assert False

    def _pretty(self, buf: List[str], prec: int, side: str) -> None:
        if self.op == 'NOT':
            buf.append('!')
            self.arg.pretty(buf, PREC_NOT, 'NONE')
        elif self.op == 'OLD':
            buf.append('old(')
            self.arg.pretty(buf, PREC_TOP, 'NONE')
            buf.append(')')
        else:
            assert False

    def free_ids(self) -> List[str]:
        return self.arg.free_ids()

def Not(e: Expr) -> Expr:
    return UnaryExpr(None, 'NOT', e)

BINOPS = {
    'AND',
    'OR',
    'IMPLIES',
    'IFF',
    'EQUAL',
    'NOTEQ'
}
z3_BINOPS: Dict[str, Callable[[z3.ExprRef, z3.ExprRef], z3.ExprRef]] = {
    'AND' : z3.And,
    'OR' : z3.Or,
    'IMPLIES' : z3.Implies,
    'IFF' : lambda x, y: x == y,
    'EQUAL' : lambda x, y: x == y,
    'NOTEQ' : lambda x, y: x != y
}

class BinaryExpr(Expr):
    def __init__(self, tok: Optional[Token], op: str, arg1: Expr, arg2: Expr) -> None:
        assert op in BINOPS
        self.tok = tok
        self.op = op
        self.arg1 = arg1
        self.arg2 = arg2

    def resolve(self, scope: Scope[InferenceSort], sort: InferenceSort) -> InferenceSort:
        check_constraint(self.tok, sort, BoolSort)

        if self.op in ['AND', 'OR', 'IMPLIES', 'IFF']:
            self.arg1.resolve(scope, BoolSort)
            self.arg2.resolve(scope, BoolSort)
        else:
            assert self.op in ['EQUAL', 'NOTEQ']
            s = self.arg1.resolve(scope, None)
            self.arg2.resolve(scope, s)

        return BoolSort


    def _denote(self) -> object:
        return (BinaryExpr, self.op, self.arg1, self.arg2)

    def __repr__(self) -> str:
        return 'BinaryExpr(%s, %s, %s)' % (self.op,
                                           repr(self.arg1),
                                           repr(self.arg2))

    def prec(self) -> int:
        if self.op == 'AND':
            return PREC_AND
        elif self.op == 'OR':
            return PREC_OR
        elif self.op == 'IMPLIES':
            return PREC_IMPLIES
        elif self.op == 'IFF':
            return PREC_IFF
        elif self.op == 'EQUAL' or self.op == 'NOTEQ':
            return PREC_EQ
        else:
            assert False

    def _pretty(self, buf: List[str], prec: int, side: str) -> None:
        p = self.prec()
        self.arg1.pretty(buf, p, 'LEFT')

        if self.op == 'AND':
            s = '&'
        elif self.op == 'OR':
            s = '|'
        elif self.op == 'IMPLIES':
            s = '->'
        elif self.op == 'IFF':
            s = '<->'
        elif self.op == 'EQUAL':
            s = '='
        elif self.op == 'NOTEQ':
            s = '!='
        else:
            assert False

        buf.append(' ')
        buf.append(s)
        buf.append(' ')

        self.arg2.pretty(buf, p, 'RIGHT')

    def free_ids(self) -> List[str]:
        x = self.arg1.free_ids()
        s = set(x)
        return x + [y for y in self.arg2.free_ids() if y not in s]

def Exists(vs: List[SortedVar], body: Expr) -> Expr:
    return QuantifierExpr(None, 'EXISTS', vs, body)

def And(*args: Expr) -> Expr:
    if len(args) == 0:
        return Bool(None, True)

    ans = args[0]
    for e in args[1:]:
        ans = BinaryExpr(None, 'AND', ans, e)

    return ans

def Eq(arg1: Expr, arg2: Expr) -> Expr:
    return BinaryExpr(None, 'EQUAL', arg1, arg2)

def Neq(arg1: Expr, arg2: Expr) -> Expr:
    return BinaryExpr(None, 'NOTEQ', arg1, arg2)

class AppExpr(Expr):
    def __init__(self, tok: Optional[Token], rel: str, args: List[Expr]) -> None:
        assert len(args) > 0
        self.tok = tok
        self.rel = rel
        self.args = args

    def resolve(self, scope: Scope[InferenceSort], sort: InferenceSort) -> InferenceSort:
        d = scope.get(self.rel)
        if d is None:
            error(self.tok, 'Unresolved relation name %s' % self.rel)

        assert isinstance(d, RelationDecl)

        check_constraint(self.tok, sort, BoolSort)

        if len(d.arity) == 0 or len(self.args) != len(d.arity):
            error(self.tok, 'Relation applied to wrong number of arguments')
        for (arg, s) in zip(self.args, d.arity):
            arg.resolve(scope, s)

        return BoolSort

    def _denote(self) -> object:
        return (AppExpr, self.rel, tuple(self.args))

    def __repr__(self) -> str:
        return 'AppExpr(%s, %s)' % (self.rel, self.args)

    def prec(self) -> int:
        return PREC_BOT

    def _pretty(self, buf: List[str], prec: int, side: str) -> None:
        buf.append(self.rel)
        buf.append('(')
        started = False
        for arg in self.args:
            if started:
                buf.append(', ')
            started = True
            arg.pretty(buf, PREC_TOP, 'NONE')
        buf.append(')')

    def free_ids(self) -> List[str]:
        l = []
        s: Set[str] = set()
        for arg in self.args:
            for x in arg.free_ids():
                if x not in s:
                    l.append(x)
                    s.add(x)
        return l

class SortedVar(object):
    def __init__(self, tok: Optional[Token], name: str, sort: Optional[Sort]) -> None:
        self.tok = tok
        self.name = name
        self.sort: InferenceSort = sort

    def resolve(self, scope: Scope[InferenceSort]) -> None:
        if self.sort is None:
            error(self.tok, 'type annotation required for variable %s' % (self.name,))

        assert not isinstance(self.sort, SortInferencePlaceholder)

        self.sort.resolve(scope)

    def __repr__(self) -> str:
        return 'SortedVar(%s, %s)' % (self.name, repr(self.sort))

    def __str__(self) -> str:
        if self.sort is None:
            return self.name
        else:
            return '%s:%s' % (self.name, self.sort)


class Binder(object):
    def __init__(self, vs: List[SortedVar]) -> None:
        self.vs = vs

    def __repr__(self) -> str:
        return 'Binder(%s)' % self.vs

    def pre_resolve(self, scope: Scope[InferenceSort]) -> None:
        for sv in self.vs:
            if sv.sort is None:
                sv.sort = SortInferencePlaceholder(sv)
            else:
                assert not isinstance(sv.sort, SortInferencePlaceholder)
                sv.sort.resolve(scope)

    def post_resolve(self) -> None:
        for sv in self.vs:
            if isinstance(sv.sort, SortInferencePlaceholder):
                error(sv.tok, 'Could not infer sort for variable %s' % (sv.name,))


class QuantifierExpr(Expr):
    def __init__(self, tok: Optional[Token], quant: str, vs: List[SortedVar], body: Expr) -> None:
        assert quant in ['FORALL', 'EXISTS']
        assert len(vs) > 0
        self.tok = tok
        self.quant = quant
        self.binder = Binder(vs)
        self.body = body

    def resolve(self, scope: Scope[InferenceSort], sort: InferenceSort) -> InferenceSort:
        check_constraint(self.tok, sort, BoolSort)

        self.binder.pre_resolve(scope)

        with scope.in_scope([(v, v.sort) for v in self.binder.vs]):
            self.body.resolve(scope, BoolSort)

        self.binder.post_resolve()

        return BoolSort

    def __repr__(self) -> str:
        return 'QuantifierExpr(%s, %s, %s)' % (self.quant, self.binder, repr(self.body))

    def _denote(self) -> object:
        return (QuantifierExpr, self.quant, self.body)

    def prec(self) -> int:
        return PREC_QUANT

    def _pretty(self, buf: List[str], prec: int, side: str) -> None:
        buf.append(self.quant.lower())
        buf.append(' ')

        started = False
        for sv in self.binder.vs:
            if started:
                buf.append(', ')
            started = True
            buf.append(str(sv))
        buf.append('. ')

        self.body.pretty(buf, PREC_QUANT, 'NONE')

    def free_ids(self) -> List[str]:
        return [x for x in self.body.free_ids() if not any(v.name == x for v in self.binder.vs)]

class Id(Expr):
    '''Unresolved symbol (might represent a constant or a variable)'''
    def __init__(self, tok: Optional[Token], name: str) -> None:
        self.tok = tok
        self.name = name

    def resolve(self, scope: Scope[InferenceSort], sort: InferenceSort) -> InferenceSort:
        d = scope.get(self.name)

        if d is None:
            error(self.tok, 'Unresolved variable %s' % (self.name,))

        if isinstance(d, RelationDecl):
            assert len(d.arity) == 0
            check_constraint(self.tok, sort, BoolSort)
            return BoolSort
        elif isinstance(d, ConstantDecl):
            check_constraint(self.tok, sort, d.sort)
            return d.sort
        else:
            v, _ = d
            check_constraint(self.tok, sort, v.sort)
            return v.sort

    def _denote(self) -> object:
        return (Id, self.name)

    def __repr__(self) -> str:
        return 'Id(%s)' % (self.name,)

    def prec(self) -> int:
        return PREC_BOT

    def _pretty(self, buf: List[str], prec: int, side: str) -> None:
        buf.append(self.name)

    def free_ids(self) -> List[str]:
        return [self.name]

Arity = List[Sort]

class UninterpretedSort(Sort):
    def __init__(self, tok: Optional[Token], name: str) -> None:
        self.tok = tok
        self.name = name
        self.decl: Optional[SortDecl] = None

    def resolve(self, scope: Scope) -> None:
        self.decl = scope.get_sort(self.name)
        if self.decl is None:
            error(self.tok, 'Unresolved sort name %s' % (self.name,))

    def __repr__(self) -> str:
        return 'UninterpretedSort(%s)' % (self.name,)

    def __str__(self) -> str:
        return self.name

    def to_z3(self) -> z3.SortRef:
        assert self.decl is not None

        return self.decl.to_z3()

    def _denote(self) -> object:
        return (UninterpretedSort, self.name)

class _BoolSort(Sort):
    def __repr__(self) -> str:
        return 'bool'

    def __str__(self) -> str:
        return 'bool'

    def resolve(self, scope: Scope) -> None:
        pass

    def to_z3(self) -> z3.SortRef:
        return z3.BoolSort()

    def _denote(self) -> object:
        return _BoolSort

BoolSort = _BoolSort()

class Decl(object):
    def __repr__(self) -> str:
        raise Exception('Unexpected decl %s does not implement __repr__ method' % type(self))

    def __str__(self) -> str:
        raise Exception('Unexpected decl %s does not implement __str__ method' % type(self))


class SortDecl(Decl):
    def __init__(self, tok: Optional[Token], name: str) -> None:
        self.tok = tok
        self.name = name
        self.z3: Optional[z3.SortRef] = None

    def resolve(self, scope: Scope) -> None:
        scope.add_sort(self.tok, self.name, self)

    def __repr__(self) -> str:
        return 'SortDecl(%s)' % self.name

    def __str__(self) -> str:
        return 'sort %s' % self.name

    def to_z3(self) -> z3.SortRef:
        if self.z3 is None:
            self.z3 = z3.DeclareSort(self.name)

        return self.z3

class RelationDecl(Decl):
    def __init__(self, tok: Optional[Token], name: str, arity: Arity, mutable: bool) -> None:
        self.tok = tok
        self.name = name
        self.arity = arity
        self.mutable = mutable
        self.mut_z3: Dict[str, Union[z3.FuncDeclRef, z3.ExprRef]] = {}
        self.immut_z3: Optional[Union[z3.FuncDeclRef, z3.ExprRef]] = None

    def resolve(self, scope: Scope) -> None:
        for sort in self.arity:
            sort.resolve(scope)

        scope.add_relation(self.tok, self.name, self)

    def __repr__(self) -> str:
        return 'RelationDecl(%s, %s, mutable=%s)' % (self.name, self.arity, self.mutable)

    def __str__(self) -> str:
        return '%s relation %s(%s)' % ('mutable' if self.mutable else 'immutable',
                                       self.name,
                                       ', '.join([str(s) for s in self.arity]))

    def to_z3(self, key: Optional[str]) -> Union[z3.FuncDeclRef, z3.ExprRef]:
        if self.mutable:
            assert key is not None
            if key not in self.mut_z3:
                if len(self.arity) > 0:
                    a = [s.to_z3() for s in self.arity] + [z3.BoolSort()]
                    self.mut_z3[key] = z3.Function(key + '_' + self.name, *a)
                else:
                    self.mut_z3[key] = z3.Const(key + '_' + self.name, z3.BoolSort())

            return self.mut_z3[key]
        else:
            if self.immut_z3 is None:
                if len(self.arity) > 0:
                    a = [s.to_z3() for s in self.arity] + [z3.BoolSort()]
                    self.immut_z3 = z3.Function(self.name, *a)
                else:
                    self.immut_z3 = z3.Const(self.name, z3.BoolSort())

            return self.immut_z3


class ConstantDecl(Decl):
    def __init__(self, tok: Optional[Token], name: str, sort: Sort, mutable: bool) -> None:
        self.tok = tok
        self.name = name
        self.sort = sort
        self.mutable = mutable
        self.mut_z3: Dict[str, z3.ExprRef] = {}
        self.immut_z3: Optional[z3.ExprRef] = None


    def __repr__(self) -> str:
        return 'ConstantDecl(%s, %s, mutable=%s)' % (self.name, self.sort, self.mutable)

    def __str__(self) -> str:
        return '%s constant %s: %s' % ('mutable' if self.mutable else 'immutable',
                                       self.name, self.sort)

    def resolve(self, scope: Scope) -> None:
        self.sort.resolve(scope)
        scope.add_constant(self.tok, self.name, self)

    def to_z3(self, key: Optional[str]) -> z3.ExprRef:
        if self.mutable:
            assert key is not None
            if key not in self.mut_z3:
                self.mut_z3[key] = z3.Const(key + '_' + self.name, self.sort.to_z3())

            return self.mut_z3[key]
        else:
            if self.immut_z3 is None:
                self.immut_z3 = z3.Const(self.name, self.sort.to_z3())

            return self.immut_z3

def close_free_vars(expr: Expr, in_scope: List[str]=[]) -> Expr:
    vs = [s for s in expr.free_ids() if s not in in_scope and s.isupper()]
    if vs == []:
        return expr
    else:
        logging.debug('closing expression')
        logging.debug(str(expr))
        logging.debug('with free vars %s' % vs)
        return QuantifierExpr(None, 'FORALL', [SortedVar(None, v, None) for v in vs], expr)

class InitDecl(Decl):
    def __init__(self, tok: Optional[Token], name: Optional[str], expr: Expr) -> None:
        self.tok = tok
        self.name = name
        self.expr = expr

    def resolve(self, scope: Scope) -> None:
        self.expr = close_free_vars(self.expr)
        self.expr.resolve(scope, BoolSort)


    def __repr__(self) -> str:
        return 'InitDecl(%s, %s)' % (self.name if self.name is not None else 'None',
                                     repr(self.expr))

    def __str__(self) -> str:
        return 'init %s%s' % (('[%s] ' % self.name) if self.name is not None else '',
                              self.expr)

class ModifiesClause(object):
    def __init__(self, tok: Optional[Token], name: str) -> None:
        self.tok = tok
        self.name = name

    def resolve(self, scope: Scope[InferenceSort]) -> None:
        d = scope.get(self.name)
        assert d is None or isinstance(d, RelationDecl) or isinstance(d, ConstantDecl)
        if d is None:
            error(self.tok, 'Unresolved constant or relation %s' % (self.name,))

    def __repr__(self) -> str:
        return 'ModifiesClause(%s)' % (self.name,)

    def __str__(self) -> str:
        return self.name

class TransitionDecl(Decl):
    def __init__(self, tok: Optional[Token], name: str, params: List[SortedVar],
                 mods: List[ModifiesClause], expr: Expr) -> None:
        self.tok = tok
        self.name = name
        self.binder = Binder(params)
        self.mods = mods
        self.expr = expr

    def resolve(self, scope: Scope) -> None:
        assert len(scope.stack) == 0

        self.binder.pre_resolve(scope)

        for mod in self.mods:
            mod.resolve(scope)

        self.expr = close_free_vars(self.expr, in_scope=[v.name for v in self.binder.vs])

        with scope.in_scope([(v, v.sort) for v in self.binder.vs]):
            self.expr.resolve(scope, BoolSort)

        self.binder.post_resolve()

    def __repr__(self) -> str:
        return 'TransitionDecl(%s, %s, %s, %s)' % (self.name, self.binder,
                                                   self.mods, repr(self.expr))

    def __str__(self) -> str:
        return 'transition %s(%s)\n  modifies %s\n  %s' % \
            (self.name,
             ', '.join([str(v) for v in self.binder.vs]),
             ', '.join([str(m) for m in self.mods]),
             self.expr)

class InvariantDecl(Decl):
    def __init__(self, tok: Optional[Token], name: Optional[str], expr: Expr) -> None:
        self.tok = tok
        self.name = name
        self.expr = expr

    def resolve(self, scope: Scope) -> None:
        self.expr = close_free_vars(self.expr)
        self.expr.resolve(scope, BoolSort)

    def __repr__(self) -> str:
        return 'InvariantDecl(%s, %s)' % (self.name if self.name is not None else 'None',
                                          repr(self.expr))

    def __str__(self) -> str:
        return 'invariant %s%s' % (('[%s] ' % self.name) if self.name is not None else '',
                                   self.expr)


class AxiomDecl(Decl):
    def __init__(self, tok: Optional[Token], name: Optional[str], expr: Expr) -> None:
        self.tok = tok
        self.name = name
        self.expr = expr

    def resolve(self, scope: Scope) -> None:
        self.expr.resolve(scope, BoolSort)

    def __repr__(self) -> str:
        self.expr = close_free_vars(self.expr)
        return 'AxiomDecl(%s, %s)' % (self.name if self.name is not None else 'None',
                                      repr(self.expr))

    def __str__(self) -> str:
        return 'axiom %s%s' % (('[%s] ' % self.name) if self.name is not None else '',
                               self.expr)




class Scope(Generic[B]):
    def __init__(self) -> None:
        self.stack: List[List[Tuple[SortedVar, B]]] = []
        self.sorts: Dict[str, SortDecl] = {}
        self.relations: Dict[str, RelationDecl] = {}
        self.constants: Dict[str, ConstantDecl] = {}

    def push(self, l: List[Tuple[SortedVar, B]]) -> None:
        self.stack.append(l)

    def pop(self) -> None:
        self.stack.pop()

    def get(self, name: str) -> Union[RelationDecl, ConstantDecl, Tuple[SortedVar, B], None]:
        # first, check for bound variables in scope
        for l in reversed(self.stack):
            for v, b in l:
                if v.name == name:
                    return (v, b)

        # otherwise, check for constants/relations (whose domains are disjoint)
        d = self.constants.get(name) or self.relations.get(name)
        return d

    def add_constant(self, tok: Optional[Token], constant: str, decl: ConstantDecl) -> None:
        assert len(self.stack) == 0

        if constant in self.constants:
            error(tok, 'Duplicate constant name %s' % (constant,))

        if constant in self.relations:
            error(tok, 'Constant name %s is already declared as a relation' %
                  (constant,))

        self.constants[constant] = decl

    def add_sort(self, tok: Optional[Token], sort: str, decl: SortDecl) -> None:
        assert len(self.stack) == 0

        if sort in self.sorts:
            error(tok, 'Duplicate sort name %s' % (sort,))

        self.sorts[sort] = decl

    def get_sort(self, sort: str) -> Optional[SortDecl]:
        return self.sorts.get(sort)

    def add_relation(self, tok: Optional[Token], relation: str, decl: RelationDecl) -> None:
        assert len(self.stack) == 0

        if relation in self.relations:
            error(tok, 'Duplicate relation name %s' % (relation,))

        if relation in self.constants:
            error(tok, 'Relation name %s is already declared as a constant' % (relation,))

        self.relations[relation] = decl

    @contextmanager
    def in_scope(self, l: List[Tuple[SortedVar, B]]) -> Iterator[None]:
        n = len(self.stack)
        self.push(l)
        yield
        self.pop()
        assert n == len(self.stack)

class Program(object):
    def __init__(self, decls: List[Decl]) -> None:
        self.decls = decls
        self.scope: Optional[Scope[InferenceSort]] = None

    def sorts(self) -> Iterator[SortDecl]:
        for d in self.decls:
            if isinstance(d, SortDecl):
                yield d

    def inits(self) -> Iterator[InitDecl]:
        for d in self.decls:
            if isinstance(d, InitDecl):
                yield d

    def invs(self) -> Iterator[InvariantDecl]:
        for d in self.decls:
            if isinstance(d, InvariantDecl):
                yield d

    def transitions(self) -> Iterator[TransitionDecl]:
        for d in self.decls:
            if isinstance(d, TransitionDecl):
                yield d

    def axioms(self) -> Iterator[AxiomDecl]:
        for d in self.decls:
            if isinstance(d, AxiomDecl):
                yield d

    def relations_and_constants(self) -> Iterator[Union[RelationDecl, ConstantDecl]]:
        for d in self.decls:
            if isinstance(d, RelationDecl) or \
               isinstance(d, ConstantDecl):
                yield d

    def decls_containing_exprs(self)\
        -> Iterator[Union[InitDecl, TransitionDecl, InvariantDecl, AxiomDecl]]:
        for d in self.decls:
            if isinstance(d, InitDecl) or \
               isinstance(d, TransitionDecl) or \
               isinstance(d, InvariantDecl) or \
               isinstance(d, AxiomDecl):
                yield d

    def resolve(self) -> None:
        self.scope = scope = Scope[InferenceSort]()

        for s in self.sorts():
            s.resolve(scope)

        for rc in self.relations_and_constants():
            rc.resolve(scope)

        for d in self.decls_containing_exprs():
            d.resolve(scope)

        assert len(scope.stack) == 0

    def __repr__(self) -> str:
        return 'Program(%s)' % (self.decls,)

    def __str__(self) -> str:
        return '\n'.join(str(d) for d in self.decls)
            