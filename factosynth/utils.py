#!/usr/bin/env python3

import itertools
import functools
import typing

import z3
if not hasattr(z3, 'Abs'):
    z3.Abs = lambda arg: z3.If(arg > 0, arg, -arg)

class Choice(dict):
    # @classmethod
    # def from_iterable(cls,*options):
    #     return cls(*itertools.chain.from_iterable(options))
    def __init__(self, *options, solver=None,**kwoptions):
        indexes = itertools.count()
        options = list(options)
        for i,option in enumerate(options):
            if isinstance(option, typing.Mapping):
                options[i] = option.items()
            elif isinstance(option, tuple):
                options[i] = [option]
            elif isinstance(option, typing.Iterable):
                options[i] = [
                    o if isinstance(o, tuple) else
                    (next(indexes),o)
                    for o in option
                ]
            else:
                options[i] = [(next(indexes),option)]
        options.append(kwoptions.items())
        options = itertools.chain.from_iterable(options)
        # options = list(options); print(options)
        super().__init__(options)
        self.choice_vars = [
            z3.FreshConst(
                z3.BoolSort(),
                prefix=f'choice:{k}'.encode("ascii", "ignore").decode(),
            )
            for k in self.keys()
        ]
        if solver is not None: solver.add(self.valid)
    @property
    def valid(self):
        if len(self)==1: return z3.BoolVal(True)
        return z3.simplify(
            z3.And(
                z3.Or(*self.choice_vars),
                z3.AtMost(*self.choice_vars, 1),
            )
        )
    def value(self, model=None, *, model_completion=False):
        if len(self)==1: return next(iter(self.values()))
        vars = self.choice_vars
        if model is not None: vars = [model.eval(var, model_completion=model_completion) for var in vars]
        for val, var in zip(self.values(), vars):
            if z3.is_true(var):
                return val
        return functools.reduce(
            lambda x,y: (z3.If(y[1],y[0],x[0]), None),
            zip(self.values(), vars),
        )[0]
        # ans = 0
        # for val,var in zip(self.values(), vars): ans = z3.If(var, val, ans)
        # return ans 
    def key(self, model=None, *, model_completion=False):
        if len(self)==1: return next(iter(self.keys()))
        vars = self.choice_vars
        if model is not None: vars = [model.eval(var, model_completion=model_completion) for var in vars]
        for key, var in zip(self.keys(), vars):
            if z3.is_true(var):
                return key
        return functools.reduce(  # will probably fail, if key is not Z3-compatible
            lambda x,y: (z3.If(y[1],y[0],x[0]), None),
            zip(self.keys(), self.choice_vars),
        )[0]
    # def simplify(self):
    #     return z3.simplify(self.value)
    def __eq__(self, ans):
        print("XXX", self, "==", ans)
        return z3.simplify(z3.And(*(
            z3.Implies(c, v == ans)
            for v,c in itertools.zip_longest(self.values(), self.choice_vars, fillvalue=True)
        )))
    def __ne__(self, ans):
        print("XXX", self, "!=", ans)
        return z3.simplify(z3.Or(*(
            z3.And(c, v != ans)
            for v,c in itertools.zip_longest(self.values(), self.choice_vars, fillvalue=True)
        )))


def is_const(expr:z3.ExprRef, const) -> z3.BoolRef:
    """Test if expression is composed of const."""
    sub1, sub2 = const.sort().cast(False), const.sort().cast(True)
    ans = z3.substitute(expr, (const,sub1)) != z3.substitute(expr, (const,sub2))
    ans = z3.simplify(ans)
    if z3.is_true(ans): ans = True
    elif z3.is_false(ans): ans = False
    return ans