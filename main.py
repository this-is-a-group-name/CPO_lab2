# lambda-terms

# Abstraction
class Abstraction:
    # λx.s init
    def __init__(self, x, s):
        # x means in, s means out, split by '.'
        self.x = x
        self.s = s

    def __str__(self):
        return "λ{}. {}".format(self.x, self.s)

    def fv(self):
        # FV(λx.s) = FV(s) - {x}
        return self.s.free() - {self.x}

    def bv(self):
        # BV(λx.s) = BV(s) U x
        return self.s.bv() | {self.x}

    def sub(self, y, t):
        # (λx.s)[y:=t] = λx.(s[y:=t])
        if y == self.x:
            return self
        return Abstraction(self.x, self.s.sub(y, t))

    # λx.x --> λy.y
    def alpha(self, y):
        if self.x == y:
            return self
        return Abstraction(y, self.s.sub(self.x, y))

    # let s beta
    def beta(self):
        return Abstraction(self.x, self.s.beta())

    # let s beta
    def eta(self):
        return Abstraction(self.x, self.s.eta())


# function application (s to an argument t)
class Application:
    # s t init
    def __init__(self, m, n):
        #
        self.m = m
        self.n = n

    def __str__(self):
        # add "( )" in order to avoid the situation: M N X and s = N,t = X,
        # if we have "( )" -> M (N X), we are no need to judge
        return "({}  {})".format(self.m, self.n)

    # FV() func, the free variable
    def fv(self):
        return self.m.fv() | self.n.fv()

    # BV() func, the bound variable
    def bv(self):
        return self.m.bv() | self.n.bv()

    # change both m and n
    def sub(self, y, t):
        return Application(self.m.sub(y, t), self.n.sub(y, t))

    # operate alpha both m and n
    def alpha(self, y):
        return Application(self.m.alpha(y), self.n.alpha(y))

    def beta(self):
        # ((M N) X) we need to calculus M N first
        if isinstance(self.m, Application):
            return Application(self.m.beta(), self.n)

        # ((λx.s) N) ≡ s[x := N]
        if isinstance(self.m, Abstraction):
            return self.m.s.sub(self.m.x, self.n)

        if isinstance(self.n, Abstraction) or isinstance(self.n, Application):
            return Application(self.m, self.n.beta())

        return self

    def eta(self):
        # (λx.M x) N --> M N
        if isinstance(self.m, Abstraction):
            if isinstance(self.m.s, Application):
                if self.m.x == self.m.s.n:
                    return Application(self.m.s.m, self.n)


# single letter
class Variable:

    def __init__(self, v):
        self.var = v

    def __str__(self):
        return str(self.var)

    def fv(self):
        return set().add(self.var)

    def bv(self):
        return set()

    def sub(self, y, t):
        if self.var == y:
            return t

        return self

    def beta(self):
        return self


# single Constant
class Constant:

    def __init__(self, c):
        self.c = c

    def __str__(self):
        return str(self.c)

    def fv(self):
        return set()

    def bv(self):
        return set()

    def sub(self, y, t):
        return self

    def beta(self):
        return self


# boolean
true = Abstraction('x', Abstraction('y', Variable('x')))
false = Abstraction('x', Abstraction('y', Variable('y')))
# pairs
e1_e2 = Abstraction('f', Application(Variable('e1'), Variable('e2')))


# create number same part
def number_n(n):
    if n > 0:
        return Application(Variable('f'), number_n(n-1))
    elif n == 0:
        return Variable('x')


# create number
def numbers(n):
    return Abstraction('f', Abstraction('x', number_n(n)))


#  n = λf. λs. f (n f s) named su2c to avoid typo
def su2c_fun(n):
    return Abstraction('f', Abstraction('x', Application(Variable('f'), Application(Application(n, Variable('f')),
                                                                                    Variable('x')))))


# m + n
def plus_fun(m, n):
    return Abstraction('f', Abstraction('x', Application(Application(m, Variable('f')),
                                                         Application(Application(n, Variable('f')), Variable('x')))))


# m * n
def multiply_fun(m, n):
    return Abstraction('f', Application(m, Application(n, Variable('f'))))


# n --
def pred(n):
    return Abstraction('f', Abstraction('x', Application(Application(
        Application(n, Abstraction('g', Abstraction('h', Application(Variable('h'), Application(
            Variable('g'), Variable('f')))))), Abstraction('u', Variable('x'))), Abstraction('u', Variable('u')))))


# T = λf. λx. f f x
# G = λg. λn. n (λu. multiply_fun n (g g (PRED n))) 1
# FACT = T G
def factorial(n):
    t = Abstraction('f', Abstraction('x', Application(Application(Variable('f'), Variable('f')), Variable('x'))))
    g = Abstraction('g', Abstraction('n', Application(Application(n, Abstraction('g', multiply_fun(n, Application(
        Application(Variable('g'), Variable('g')), pred(n))))), numbers(1))))
    return Application(t, g)


#  is_zero n =λn.n (λx.false) true
def is_zero(n):
    return Application(Application(n, Abstraction("x", false)), true)


# for beta process
def process(test):
    while true:
        print(test)
        temp = test.beta()
        if str(test) == str(temp):
            break
        test = temp
    return test


if __name__ == '__main__':

    # test for su2c:1++ -->2
    print(str(process(su2c_fun(numbers(1)))) == str(numbers(2)))

    # test2 for plus:1+1=2
    print(str(process(plus_fun(numbers(1), numbers(2)))) == str(numbers(3)))

    # test3 for multiply:2*3=6
    print(str(process(multiply_fun(numbers(2), numbers(3)))) == str(numbers(6)))

    # test4 for pred:2-1=1
    print(str(process(pred(numbers(2)))) == str(numbers(1)))

    # # test5 for factorial:2! = 2
    # print(str(process(factorial(numbers(2))))[4:] == str(numbers(2)))

    # test6 for is_zero:
    print(str(process(is_zero(numbers(0)))) == str(true))
    print(str(process(is_zero(numbers(1)))) == str(true))
