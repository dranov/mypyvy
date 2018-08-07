from typing import List, Optional, Any, Union, Iterable, Sequence, Iterator, Protocol

class CheckSatResult: ...

sat: CheckSatResult
unsat: CheckSatResult

class Z3PPObject: ...
class Context: ...
class ModelRef(Z3PPObject):
    def decls(self) -> List[FuncDeclRef]: ...
    def sorts(self) -> List[SortRef]: ...
    def get_universe(self, s: SortRef) -> Sequence[ExprRef]: ...
    def eval(self, e: ExprRef) -> ExprRef: ...



class Solver(Z3PPObject):
#    def __setattr__(self, name: str, value: Any) -> None: ...
    def __enter__(self) -> None: ...
    def __exit__(self, exn_type: Any, exn_value: Any, traceback: Any) -> None: ...
    def add(self, *args: ExprRef) -> None: ...
    def check(self, *args: ExprRef) -> CheckSatResult: ...
    def model(self) -> ModelRef: ...
    def to_smt2(self) -> str: ...
    def unsat_core(self) -> Sequence[ExprRef]: ...


class AstRef(Z3PPObject): ...
class SortRef(AstRef): ...
class ExprRef(AstRef):
      def __eq__(self, other: ExprRef) -> ExprRef: ... # type: ignore
      def __ne__(self, other: ExprRef) -> ExprRef: ... # type: ignore
      def sort(self) -> SortRef: ...
      def decl(self) -> FuncDeclRef: ...

class FuncDeclRef(AstRef):
      def __call__(self, *args: ExprRef) -> ExprRef: ...
      def arity(self) -> int: ...
      def domain(self, i: int) -> SortRef: ...
      def range(self) -> SortRef: ...
      def name(self) -> str: ...


def Function(name: str, *args: SortRef) -> FuncDeclRef: ...
def Bool(name: str) -> ExprRef: ...
def Const(name: str, sort: SortRef) -> ExprRef: ...
def Consts(names: str, sort: SortRef) -> List[ExprRef]: ...
def DeclareSort(name: str, ctx: Optional[Context] = ...) -> SortRef: ...
def BoolSort(ctx: Optional[Context] = ...) -> SortRef: ...

def Not(arg: ExprRef) -> ExprRef: ...
def And(*args: ExprRef) -> ExprRef: ...
def Or(*args: ExprRef) -> ExprRef: ...
def Implies(a: ExprRef, b: ExprRef) -> ExprRef: ...

def BoolVal(x: bool) -> ExprRef: ...

def ForAll(vs: Union[ExprRef, List[ExprRef]], body: ExprRef) -> ExprRef: ...
def Forall(vs: Union[ExprRef, List[ExprRef]], body: ExprRef) -> ExprRef: ...
def Exists(vs: Union[ExprRef, List[ExprRef]], body: ExprRef) -> ExprRef: ...


def main_ctx() -> Context: ...

def set_param(*args: Any) -> None: ...
