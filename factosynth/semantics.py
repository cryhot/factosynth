#!/usr/bin/env python3

import itertools
import functools
import typing
import abc

import z3

from .utils import *

BITS = 32
Int32Sort = z3.BitVecSort(BITS)
ZERO = Int32Sort.cast(0)

class Operator(abc.ABC):
    """Simple function that takes z3 primitives as input and returns a z3 primitive as output."""
    @property
    @abc.abstractmethod
    def args(self) -> typing.Sequence[z3.ExprRef]: raise NotImplementedError
    @property
    @abc.abstractmethod
    def operators(self) -> typing.Mapping[str,z3.ExprRef]: raise NotImplementedError
    def __init__(self, operator=None, *, solver=None):
        if isinstance(operator, str): operator = [operator]
        if operator is None: operator = list(self.operators.keys())
        self.choice = Choice(
            (op, self.operators[op])
            for op in operator
        )
        if solver is not None: solver.add(self.valid)
    @classmethod
    def from_json(cls, obj):
        return cls(obj)
    def to_json(self):
        return self.choice.key()
    def __call__(self, *args, model=None, model_completion=False):
        eval_kwargs = dict(model=model, model_completion=model_completion)
        args = list(args)
        for i,arg in enumerate(args):
            if not isinstance(arg,z3.ExprRef): args[i] = Int32Sort.cast(arg)
        ans = z3.substitute(
            self.choice.value(**eval_kwargs),
            *(
                (var, val)
                for var, val in zip(self.args, args)
            )
        )
        ans = z3.simplify(ans)
        return ans
    @property
    def valid(self):
        return self.choice.valid
    def eval(self, model, model_completion=False):
        eval_kwargs = dict(model=model, model_completion=model_completion)
        # eval_kwargs.update(model_completion=True)
        # print(self.choice)
        # print(self.choice.value(**eval_kwargs))
        # print(model)
        # print("ValidR:", self.choice.valid)
        # print("Valid:", model.eval(self.choice.valid))
        return self.__class__(
            operator=self.choice.key(**eval_kwargs),
        )
class Comparator(Operator):
    args = a,b = z3.Consts('A B', Int32Sort)
    operators = {
        '>': a>b,
        '<': a<b,
        '=': a==b,
        '≥': a>=b,
        '≤': a<=b,
        '≠': a!=b,
    }
class Operation(Operator):
    args = a,b = z3.Consts('A B', Int32Sort)
    operators = {
        '*': a*b,
        '/': z3.If(b!=0, a/b, 0),
        '+': a+b,
        '-': a-b,
        '%': z3.If(b!=0, z3.SRem(a,b), 0),
        '^': z3.Int2BV(z3.BV2Int(a,True) ** z3.BV2Int(b,True), BITS),
        '<<': a<<(b%BITS),
        '>>': a>>(b%BITS),
        'AND': a&b,
        'OR': a|b,
        'XOR': a^b,
    }


class Signal(dict):
    """https://lua-api.factorio.com/latest/Concepts.html#SignalID"""
    def __init__(self, type, name):
        super().__init__(
            type=type,
            name=name,
        )
    
    def __str__(self) -> str:
        return self._repr_rich()
    
    def _repr_rich(self, count=None) -> str:
        """See https://wiki.factorio.com/Rich_text."""
        type = self.type
        if type == 'virtual': type = 'virtual-signal'
        count = "" if count is None else f":{count}"
        return f"[{type}={self.name}{count}]"
    
    def _repr_char(self, count=None) -> str:
        """Return a unique character representing this."""
        if self.type == "item": return 'i'
        if self.type == "fluid": return 'f'
        if self.type == "virtual":
            import re
            match = re.fullmatch(r'signal-(?P<char>[A-Z0-9])', self.name)
            if match: return match.group('char')
            if self.name in [
                "signal-everything",
                "signal-anything",
                "signal-each",
            ]:
                return '*'
            return 's'
        return '?'
    
    def _repr_cchar(self, count=None) -> str:
        from termcolor import colored
        if self.type == "item":
            return colored('i', color="yellow", on_color="on_grey", attrs=None)
        elif self.type == "fluid":
            return colored('f', color="cyan", on_color="on_grey", attrs=None)
        elif self.type == "virtual":
            import re
            match = re.fullmatch(r'signal-((?P<char>[A-Z0-9])|(?P<signal>[a-z]+))', self.name)
            char, signal = match.group('char'), match.group('signal')
            if match:
                if char: return colored(char, color="grey", on_color="on_blue",    attrs=['dark'])
                if signal == "everything": return colored('*', color="grey", on_color="on_red",    attrs=['dark'])
                if signal == "anything":   return colored('*', color="grey", on_color="on_green",  attrs=['dark'])
                if signal == "each":       return colored('*', color="grey", on_color="on_yellow", attrs=['dark'])
                c = ' ' if signal == 'blue' else '\u2591'
                if signal in ['red', 'green', 'blue', 'yellow', 'cyan', 'white']:
                    return colored(c, color=f"{signal}", on_color=f"on_{signal}", attrs=[])
                if signal == "pink":
                    return colored('\u2592', color=f"magenta", on_color=f"on_magenta", attrs=['bold'])
                if signal == "grey":  return colored('\u2592', color="grey", on_color="on_grey", attrs=['bold'])
                if signal == "black": return colored('\u2591', color="grey", on_color="on_grey", attrs=['dark'])
                if signal == "check": return colored('\u2713', color="green", on_color="on_grey", attrs=['bold'])
                if signal == "info": return colored('\u2139', color="blue", on_color="on_grey", attrs=['bold'])
                if signal == "dot": return colored('\u22C5', color="white", on_color="on_grey", attrs=['bold'])
                return colored('!', color="red", on_color="on_grey", attrs=None)
            return colored('s', color="red", on_color="on_grey", attrs=None)
        else:
            return colored('?', color="grey", on_color="on_grey", attrs=['dark', 'bold'])

    
    def __format__(self, fmt) -> str:
        if not isinstance(fmt, str):
            raise TypeError("must be str, not %s" % type(fmt).__name__)
        if len(fmt) != 0:
            return self.strftime(fmt)
        return str(self)
    
    @classmethod
    def from_char(cls, char, capitalize=True):
        import unicodedata as ud
        import string
        char = ud.normalize('NFD', char)[0]
        if ud.category(char) == 'Mn':
            return None
        if capitalize: char = char.upper()
        if char in string.ascii_uppercase or char in string.digits:
            return cls('virtual', f'signal-{char}')
        elif char in string.whitespace:
            return cls('virtual', 'signal-blue')
        return None
    
    dict_name = {
        "virtual": [
            "signal-red",
            "signal-green",
            "signal-blue",
            "signal-yellow",
            "signal-pink",
            "signal-cyan",
            "signal-white",
            "signal-grey",
            "signal-black",
            "signal-check",
            "signal-info",
            "signal-dot",
            "signal-everything",
            "signal-anything",
            "signal-each",
        ]
    }

    @classmethod
    def from_name(cls, *args):
        """sanitize name"""
        type = None
        if len(args)==1: name, = args
        elif len(args)==2: type,name, = args
        else: raise TypeError(f"from_name expected between 1 and 2 arguments, got {len(args)}")
        if type == "virtual-signal": type = "virtual"
        if type == "signal": type = "virtual"
        if type in ["virtual",None] and len(name)==1:
            signal = cls.from_char(name)
            if signal is not None: return signal
        for type2, names in cls.dict_name.items():
            if type not in [None,type2]: continue
            if name in names: return cls(type2, name)
            if type2 == "virtual":
                if not "signal-" in name:
                    signal = cls.from_name(type2, f'signal-{name}')
                    if signal is not None: return signal
                if "magenta" in name:
                    signal = cls.from_name(type2, name.replace("magenta","pink"))
                    if signal is not None: return signal
        if " " in name:
            signal = cls.from_name(type, name.replace(" ","-"))
            if signal is not None: return signal
        return None

    @classmethod
    def from_rich(cls, string:str, count=False):
        """See https://wiki.factorio.com/Rich_text.
        count: can be
            - False: disable count parsing, return `signal`
            - True, None or int: enable count parsing (default to `1`, `None` or integer count), return `signal,count`
        """
        import re
        if count is True: count=1
        if count is False: count_regex = r''
        else:              count_regex = r'(:(?P<count>[-+]?\d*))?'

        # regex = r'\[(?P<type>item|fluid|virtual(-signal)?|entity)=(?P<name>(\w|-)+)' + count_regex + r'\]'
        regex = r'\[((?P<type>item|fluid|virtual(-signal)?|entity)=)?(?P<name>(\w|-)+)' + count_regex + r'\]'
        match = re.fullmatch(regex, string)
        if match:
            type = match.group('type')
            if type == "virtual-signal": type = "virtual"
            name = match.group('name')
            if True: # sanitize
                signal = cls.from_name(type, name)
                if signal is not None: type, name = signal.type, signal.name
            if type is None or name is None: signal = None
            else: signal = Signal(type, name)
            if count is not False and match.group('count') is not None:
                count = int(match.group('count'))
            if count is False: return signal
            else: return (signal, count)
        print(string)
        if count is False: return None
        else: return (None, count)

signals = []

EACH = each = "each"
ANYTHING = anything = "anything"
EVERYTHING = everything = "everything"

def SignalConst(name, is_value=True):
    """Returns the cannonical z3 constant for signal value/presence placeholder."""
    if is_value:
        return z3.Const(f'SIGNAL:{name}', Int32Sort)  # value placeholder
    else:
        return z3.Const(f'SIGNAL?:{name}', z3.BoolSort())  # presence placeholder
class Register(dict):
    """A register is a mapping from signals (str|Signal) to counts (z3.BitVecRef)."""
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        for signal, count in self.items():
            if not isinstance(count,z3.ExprRef):
                # self[signal] = count = Int32Sort.cast(count)
                count = Int32Sort.cast(count)
                super().__setitem__(signal, count)
    @classmethod
    def fromkeys(cls, signals, count=None):
        """ Returns a new Register with signals from iterable and counts equal to `count`.
            If `count` is not given, fresh z3 constants are used instead.
        """
        if count is None:
            return cls(
                (signal, z3.FreshConst(Int32Sort, prefix=f'count:{signal}'))
                for signal in signals
            )
        return super().fromkeys(signals, count)
    def copy(self):
        return self.__class__(self)
    @classmethod
    def sum(cls, *args):
        """Point-wise sum of registers."""
        signals = set(signal
            for reg in args
            for signal in reg.keys()
        )
        ans = cls(
            (signal, z3.Sum(*(
                reg[signal]
                for reg in args
                if signal in reg.keys()
            )))
            for signal in signals
        )
        return ans
    def __add__(self, other):
        if isinstance(other, __class__): return __class__.sum(self, other)
        return NotImplemented
    def __and__(self, other):
        if isinstance(other, z3.BoolRef):
            ans = self.__class__(
                (signal, z3.If(other,count,0))
                for signal, count in self.items()
            )
            return ans
        raise TypeError()
    def __rand__(self, other): return self.__and__(other)
    def __eq__(self, reg) -> bool:
        if isinstance(reg, typing.Mapping):
            signals = set(self.keys()) | set(reg.keys())
            ans = z3.And([
                self.get(signal, 0) == reg.get(signal, 0)
                for signal in signals
            ])
        else:
            ans = z3.And(
                count == reg
                for signal, count in self.items()
            )
        ans = z3.simplify(ans, bv_ite2id=True)
        if z3.is_true(ans): ans = True
        elif z3.is_false(ans): ans = False
        return ans
    def __ne__(self, reg) -> bool:
        ans = z3.Not(self.__eq__(reg))
        ans = z3.simplify(ans)
        if z3.is_true(ans): ans = True
        elif z3.is_false(ans): ans = False
        return ans
    def __getitem__(self, signal):
        if not isinstance(signal, z3.ExprRef) and signal == EACH: signal = SignalConst(EACH)
        if isinstance(signal, z3.ExprRef):
            each_count = Int32Sort.cast(0)
            for var, val in self.items():
                each_count = z3.If(SignalConst(var,False),val,each_count)
            ans = z3.substitute( signal,
                *(
                    (SignalConst(var), val)
                    for var, val in self.items()
                ),
                (SignalConst(EACH), each_count)
            )
            return ans
        if signal not in self.keys(): return ZERO  # default
        return super().__getitem__(signal)
    def __setitem__(self, signal, count):
        """If using SignalConst, make sure to use z3.BoolSort()."""
        if not isinstance(count,z3.ExprRef): count = Int32Sort.cast(count)
        if isinstance(signal, z3.ExprRef):
            # TODO: get list of free f"signal:{var}" variable in `signal` argument
            # 1) substitute even non-registered signals
            # 2) do not set items that are not referenced in argument
            for s,c in self.items():
                self[s] = z3.If(
                    z3.substitute( signal,
                        *(
                            (SignalConst(var,False), z3.BoolVal(var==s))
                            for var in self.keys()
                        ),
                        (SignalConst(EACH,False), z3.BoolVal(True)),
                        # (SignalConst(EACH,False), c!=0),
                        # (SignalConst(EACH), count),
                    ),
                    z3.substitute( count,
                        *(
                            (SignalConst(var,False), z3.BoolVal(var==s))
                            for var in self.keys()
                        ),
                        (SignalConst(EACH), c),
                    ),
                    c,
                )
            return
        else:
            s,c = signal, self[signal]
            count = z3.substitute( count,
                *(
                    (SignalConst(var,False), z3.BoolVal(var==s))
                    for var in self.keys()
                ),
                (SignalConst(EACH), c),
            )
            return super().__setitem__(signal, count)
    def setdefault(self, key, default):
        if not isinstance(default,z3.ExprRef): default = Int32Sort.cast(default)
        return super().setdefault(key, default)
    def update(self, other={}, **kwargs):
        # assert other is None or isinstance(other, __class__) # TODO: sanitize other
        for s,c in kwargs.items():
            if not isinstance(c,z3.ExprRef): kwargs[s] = c = Int32Sort.cast(c)
        super().update(other, **kwargs)
        for signal, count in self.items():
            if not isinstance(count,z3.ExprRef):
                # self[signal] = count = Int32Sort.cast(count)
                count = Int32Sort.cast(count)
                super().__setitem__(signal, count)
    def simplify(self, *args, bv2int=False, **kwargs):
        def simplify(expr):
            if bv2int and isinstance(expr, z3.BitVecRef):
                expr = z3.BV2Int(expr, is_signed=True)
            expr = z3.simplify(expr, *args, **kwargs)
            return expr
        ans = self.__class__(
            (signal, simplify(count))
            for signal, count in self.items()
        )
        return ans




class ControlBehavior(abc.ABC):
    def __init__(self, *, solver=None):
        if solver is not None: solver.add(self.valid)
    @abc.abstractmethod
    def __call__(self, input:Register, *, model=None, model_completion=False, solver=None):
        """If a solver is passed, create temporary variables."""
        if solver is not None:
            ans = Register.fromkeys(input) # fresh constants
            solver.add(ans==input)
        else:
            ans = input.copy()
        return ans
    @property
    def valid(self):
        return z3.BoolVal(True)
    @abc.abstractmethod
    def eval(self, model, model_completion=False):
        raise NotImplementedError()

class DeciderControlBehavior(ControlBehavior):
    def __init__(self,
        first_signal=None, # signal constant
        comparator=None,
        second_signal=None, # signal constant or other constant
        output_signal=None,
        copy_count_from_input=None,
        *,
        signals=None,
        solver=None,
    ):
        if not isinstance(comparator, Operator):
            comparator = Comparator(comparator)

        if not isinstance(first_signal,Choice):
            if first_signal is None: first_signal = [*signals,EVERYTHING,ANYTHING,EACH]  # default
            if isinstance(first_signal, (str,Signal,int,z3.ExprRef)): first_signal = [first_signal]
            options = list(first_signal)
            for i,option in enumerate(options):
                if isinstance(option, (str,Signal)): options[i] = option = SignalConst(option)
                if isinstance(option, int): options[i] = option = Int32Sort.cast(option)
            first_signal = Choice(options)
        
        if not isinstance(second_signal,Choice):
            if second_signal is None: second_signal = [z3.FreshConst(Int32Sort, prefix='const'), *signals]  # default
            if isinstance(second_signal, (str,Signal,int,z3.ExprRef)): second_signal = [second_signal]
            options = list(second_signal)
            for i,option in enumerate(options):
                if isinstance(option, (str,Signal)): options[i] = option = SignalConst(option)
                if isinstance(option, int): options[i] = option = Int32Sort.cast(option)
            second_signal = Choice(options)
        
        if not isinstance(output_signal,Choice):
            if output_signal is None: output_signal = [*signals,EVERYTHING,ANYTHING,EACH]  # default
            if isinstance(output_signal, (str,Signal,int,z3.ExprRef)): output_signal = [output_signal]
            options = list(output_signal)
            for i,option in enumerate(options):
                if isinstance(option, (str,Signal)): options[i] = option = SignalConst(option,False)
                if isinstance(option, int): options[i] = option = Int32Sort.cast(option)
            output_signal = Choice(options)
        
        if copy_count_from_input is None:
            copy_count_from_input = z3.FreshConst(z3.BoolSort(), prefix=f'copy_count')
        if not isinstance(copy_count_from_input, z3.ExprRef): copy_count_from_input = z3.BoolSort().cast(copy_count_from_input)
        
        self.first_signal = first_signal
        self.second_signal = second_signal
        self.comparator = comparator
        self.output_signal = output_signal
        self.copy_count_from_input = copy_count_from_input
        super().__init__(solver=solver)
    @property
    def valid(self):
        first_signal = self.first_signal.value()
        output_signal = self.output_signal.value()
        return z3.And(
            super().valid,
            z3.Implies(is_const(output_signal,SignalConst(ANYTHING)), is_const(first_signal,SignalConst(ANYTHING))),
            z3.Implies(is_const(output_signal,SignalConst(EACH)), is_const(first_signal,SignalConst(EACH))),
            z3.Implies(is_const(output_signal,SignalConst(EVERYTHING)), z3.Not(is_const(first_signal,SignalConst(EACH)))),
            self.first_signal.valid,
            self.second_signal.valid,
            self.comparator.valid,
            self.output_signal.valid,
        )
    def __call__(self, input:Register, *, model=None, model_completion=False, solver=None):
        eval_kwargs = dict(model=model, model_completion=model_completion)
        first_signal = self.first_signal.value(**eval_kwargs)
        second_signal = self.second_signal.value(**eval_kwargs)
        output_signal = self.output_signal.value(**eval_kwargs)
        decision = self.comparator(first_signal, second_signal)
        decision = z3.If(
            is_const(first_signal, SignalConst(EVERYTHING)),
            z3.And([
                z3.Implies(SignalConst(var)!=0, self.comparator(SignalConst(var), second_signal))
                for var in input.keys()
            ]),
            decision,
        )
        decision = z3.If(
            is_const(first_signal, SignalConst(ANYTHING)),
            z3.Or([
                z3.And(SignalConst(var)!=0, self.comparator(SignalConst(var), second_signal))
                for var in input.keys()
            ]),
            decision,
        )
        decision = input[decision]
        decision = z3.simplify(decision, bv_ite2id=True)
        is_sum = z3.And(
            is_const(first_signal, SignalConst(EACH)),
            z3.Not(is_const(output_signal, SignalConst(EACH,False))),
        )
        ans = Register.fromkeys(input,0)
        chosen = []
        for signal,count in input.items():
            output_count = z3.If(self.copy_count_from_input, count, Int32Sort.cast(1))
            is_output = z3.substitute(output_signal,
                *(
                    (SignalConst(var,False), z3.BoolVal(var==signal))
                    for var in input.keys()
                ),
                (SignalConst(EACH,False), count!=0),
                (SignalConst(EVERYTHING,False), count!=0),
                (SignalConst(ANYTHING,False), z3.And(count!=0, z3.Not(z3.Or(chosen)))),
            )
            is_output = z3.If(is_sum, count!=0, is_output)
            ans[signal] = z3.If(z3.And(is_output,decision), output_count, ZERO)
            chosen.append(z3.And(is_output,decision))
        ans[is_sum] = z3.If(output_signal,z3.Sum(*ans.values()),0)
        for signal,count in ans.items(): # sanitize output: remove local constants
            ans[signal] = z3.substitute( count,
                *(
                    (SignalConst(var), ZERO)
                    for var in ans.keys()
                ),
                (SignalConst(EVERYTHING), ZERO),
                (SignalConst(ANYTHING), ZERO),
                (SignalConst(EVERYTHING,False), z3.BoolVal(False)),
                (SignalConst(ANYTHING,False), z3.BoolVal(False)),
            )
        ans = ans.simplify(bv_ite2id=True)
        return super().__call__(ans, model=model, model_completion=model_completion, solver=solver)
    def eval(self, model, model_completion=False):
        eval_kwargs = dict(model=model, model_completion=model_completion)
        return self.__class__(
            first_signal=model.eval(self.first_signal.value(**eval_kwargs), model_completion=model_completion),
            comparator=self.comparator.eval(**eval_kwargs),
            second_signal=model.eval(self.second_signal.value(**eval_kwargs), model_completion=model_completion),
            output_signal=model.eval(self.output_signal.value(**eval_kwargs), model_completion=model_completion),
            copy_count_from_input=model.eval(self.copy_count_from_input, model_completion=model_completion),
        )

    def to_cnide(self):
        """See also: https://github.com/charredUtensil/cnide"""
        first_value = self.first_signal.value()
        if z3.is_bv_value(first_value): first_value = z3.simplify(z3.BV2Int(first_value, is_signed=True))
        if z3.is_const(first_value): first_value = str(first_value).replace("SIGNAL:","")
        second_value = self.second_signal.value()
        if z3.is_bv_value(second_value): second_value = z3.simplify(z3.BV2Int(second_value, is_signed=True))
        if z3.is_const(second_value): second_value = str(second_value).replace("SIGNAL:","")
        output_value = self.output_signal.value()
        if z3.is_const(output_value): output_value = str(output_value).replace("SIGNAL?:","")
        ans = f"""{first_value} {self.comparator.to_json()} {second_value} then {"" if self.copy_count_from_input else "1 as "}{output_value}"""
        return ans

class ArithmeticControlBehavior(ControlBehavior):
    def __init__(self,
        first_signal=None, # signal constant or other constant
        operation=None,
        second_signal=None, # signal constant or other constant
        output_signal=None,
        *,
        signals=None,
        solver=None,
    ):
        if not isinstance(operation, Operator):
            operation = Operation(operation)

        if not isinstance(first_signal,Choice):
            if first_signal is None: first_signal = [z3.FreshConst(Int32Sort, prefix='const'), *signals, EACH]  # default
            if isinstance(first_signal, (str,Signal,int,z3.ExprRef)): first_signal = [first_signal]
            options = list(first_signal)
            for i,option in enumerate(options):
                if isinstance(option, (str,Signal)): options[i] = option = SignalConst(option)
                if isinstance(option, int): options[i] = option = Int32Sort.cast(option)
            first_signal = Choice(options)
        
        if not isinstance(second_signal,Choice):
            if second_signal is None: second_signal = [z3.FreshConst(Int32Sort, prefix='const'), *signals, EACH]  # default
            if isinstance(second_signal, (str,Signal,int,z3.ExprRef)): second_signal = [second_signal]
            options = list(second_signal)
            for i,option in enumerate(options):
                if isinstance(option, (str,Signal)): options[i] = option = SignalConst(option)
                if isinstance(option, int): options[i] = option = Int32Sort.cast(option)
            second_signal = Choice(options)
        
        if not isinstance(output_signal,Choice):
            if output_signal is None: output_signal = [*signals,EACH]  # default
            if isinstance(output_signal, (str,Signal,int,z3.ExprRef)): output_signal = [output_signal]
            options = list(output_signal)
            for i,option in enumerate(options):
                if isinstance(option, (str,Signal)): options[i] = option = SignalConst(option,False)
                if isinstance(option, int): options[i] = option = Int32Sort.cast(option)
            output_signal = Choice(options)
        
        self.first_signal = first_signal
        self.second_signal = second_signal
        self.operation = operation
        self.output_signal = output_signal
        super().__init__(solver=solver)
    @property
    def valid(self):
        first_signal = self.first_signal.value()
        second_signal = self.second_signal.value()
        output_signal = self.output_signal.value()
        return z3.And(
            super().valid,
            z3.Implies(is_const(output_signal,SignalConst(EACH)), z3.Or(is_const(first_signal,SignalConst(EACH)), is_const(second_signal,SignalConst(EACH)))),
            z3.Or(z3.Not(is_const(first_signal,SignalConst(EACH))), z3.Not(is_const(second_signal,SignalConst(EACH)))),
            self.first_signal.valid,
            self.second_signal.valid,
            self.operation.valid,
            self.output_signal.valid,
        )
    def __call__(self, input:Register, *, model=None, model_completion=False, solver=None):
        eval_kwargs = dict(model=model, model_completion=model_completion)
        first_signal = self.first_signal.value(**eval_kwargs)
        second_signal = self.second_signal.value(**eval_kwargs)
        output_signal = self.output_signal.value(**eval_kwargs)
        output_count = self.operation(first_signal, second_signal)
        output_count = input[output_count]
        output_count = z3.simplify(output_count, bv_ite2id=True)
        is_sum = z3.And(
            z3.Or(is_const(first_signal, SignalConst(EACH)), is_const(second_signal, SignalConst(EACH))),
            z3.Not(is_const(output_signal, SignalConst(EACH,False))),
        )
        ans = Register.fromkeys(input,0)
        for signal,count in input.items():
            is_output = z3.substitute(output_signal,
                *(
                    (SignalConst(var,False), z3.BoolVal(var==signal))
                    for var in input.keys()
                ),
                (SignalConst(EACH,False), count!=0),
            )
            is_output = z3.If(is_sum, count!=0, is_output)
            ans[signal] = z3.If(is_output, output_count, ZERO)
        ans[is_sum] = z3.If(output_signal,z3.Sum(*ans.values()),0)
        for signal,count in ans.items(): # sanitize output: remove local constants
            ans[signal] = z3.substitute( count,
                *(
                    (SignalConst(var), ZERO)
                    for var in ans.keys()
                ),
            )
        ans = ans.simplify(bv_ite2id=True)
        return super().__call__(ans, model=model, model_completion=model_completion, solver=solver)
    def eval(self, model, model_completion=False):
        eval_kwargs = dict(model=model, model_completion=model_completion)
        return self.__class__(
            first_signal=model.eval(self.first_signal.value(**eval_kwargs), model_completion=model_completion),
            operation=self.operation.eval(**eval_kwargs),
            second_signal=model.eval(self.second_signal.value(**eval_kwargs), model_completion=model_completion),
            output_signal=model.eval(self.output_signal.value(**eval_kwargs), model_completion=model_completion),
        )

    def to_cnide(self):
        """See also: https://github.com/charredUtensil/cnide"""
        first_value = self.first_signal.value()
        if z3.is_bv_value(first_value): first_value = z3.simplify(z3.BV2Int(first_value, is_signed=True))
        if z3.is_const(first_value): first_value = str(first_value).replace("SIGNAL:","")
        second_value = self.second_signal.value()
        if z3.is_bv_value(second_value): second_value = z3.simplify(z3.BV2Int(second_value, is_signed=True))
        if z3.is_const(second_value): second_value = str(second_value).replace("SIGNAL:","")
        output_value = self.output_signal.value()
        if z3.is_const(output_value): output_value = str(output_value).replace("SIGNAL?:","")
        ans = f"""{first_value} {self.operation.to_json()} {second_value} as {output_value}"""
        return ans



# class Entity:
#     pass
# class Combinator(Entity):
#     pass
# class ConstantCombinator(Combinator):
#     pass



