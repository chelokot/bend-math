#!/usr/bin/env python3
"""Search an exact certificate for `0 <= goal` and print it as a Bend term.

The certificate has the shape checked by `Certificate.nonnegative`:

    (1 + denominator) * goal = sum of  c * (product of facts) * square^2
                             + sum of  multiplier * equation

where every fact is a polynomial known to be nonnegative, every equation is a
polynomial known to be zero, the coefficients c are natural numbers and the
multipliers are polynomials with integer coefficients. The search solves an
exact linear program over the rationals.

Polynomials are written with `+`, `-`, `*`, `^`, integer literals,
parentheses and the given variable names.
"""
import argparse
import itertools
import json
import math
import re
import sys
from fractions import Fraction


class Expr:
    pass


class Var(Expr):
    def __init__(self, index):
        self.index = index


class Num(Expr):
    def __init__(self, value):
        self.value = value


class Add(Expr):
    def __init__(self, left, right):
        self.left, self.right = left, right


class Mul(Expr):
    def __init__(self, left, right):
        self.left, self.right = left, right


class Neg(Expr):
    def __init__(self, body):
        self.body = body


def parse(text, names):
    tokens = re.findall(r"\d+|[A-Za-z_][A-Za-z_0-9]*|[-+*^()]", text)
    position = 0

    def peek():
        return tokens[position] if position < len(tokens) else None

    def take(expected=None):
        nonlocal position
        token = tokens[position]
        if expected is not None and token != expected:
            raise ValueError(f"expected {expected!r}, found {token!r} in {text!r}")
        position += 1
        return token

    def atom():
        token = peek()
        if token == "(":
            take("(")
            inner = sum_()
            take(")")
            return inner
        if token == "-":
            take("-")
            return Neg(power())
        take()
        if token.isdigit():
            return Num(int(token))
        if token not in names:
            raise ValueError(f"unknown variable {token!r} in {text!r}")
        return Var(names.index(token))

    def power():
        base = atom()
        if peek() == "^":
            take("^")
            exponent = int(take())
            result = base
            for _ in range(exponent - 1):
                result = Mul(result, base)
            return result
        return base

    def product():
        result = power()
        while peek() == "*":
            take("*")
            result = Mul(result, power())
        return result

    def sum_():
        result = product()
        while peek() in ("+", "-"):
            if take() == "+":
                result = Add(result, product())
            else:
                result = Add(result, Neg(product()))
        return result

    result = sum_()
    if position != len(tokens):
        raise ValueError(f"unexpected {tokens[position]!r} in {text!r}")
    return result


def poly(expr, count):
    if isinstance(expr, Var):
        exponents = [0] * count
        exponents[expr.index] = 1
        return {tuple(exponents): Fraction(1)}
    if isinstance(expr, Num):
        return {(0,) * count: Fraction(expr.value)} if expr.value else {}
    if isinstance(expr, Neg):
        return {m: -c for m, c in poly(expr.body, count).items()}
    left, right = poly(expr.left, count), poly(expr.right, count)
    if isinstance(expr, Add):
        return add(left, right)
    return mul(left, right)


def add(left, right):
    result = dict(left)
    for m, c in right.items():
        result[m] = result.get(m, 0) + c
        if result[m] == 0:
            del result[m]
    return result


def mul(left, right):
    result = {}
    for (m1, c1), (m2, c2) in itertools.product(left.items(), right.items()):
        m = tuple(a + b for a, b in zip(m1, m2))
        result[m] = result.get(m, 0) + c1 * c2
        if result[m] == 0:
            del result[m]
    return result


def degree(p):
    return max((sum(m) for m in p), default=0)


def bend(expr):
    if isinstance(expr, Var):
        return f"R.Variable{{{expr.index}n}}"
    if isinstance(expr, Num):
        return f"R.Number{{{expr.value}n}}"
    if isinstance(expr, Neg):
        return f"R.Negate{{{bend(expr.body)}}}"
    constructor = "R.Plus" if isinstance(expr, Add) else "R.Multiply"
    return f"{constructor}{{{bend(expr.left)}, {bend(expr.right)}}}"


def poly_expr(p):
    terms = []
    for m, c in sorted(p.items()):
        factors = [Var(i) for i, e in enumerate(m) for _ in range(e)]
        body = Num(abs(c.numerator))
        for factor in factors:
            body = Mul(body, factor)
        terms.append(body if c > 0 else Neg(body))
    if not terms:
        return Num(0)
    result = terms[0]
    for term in terms[1:]:
        result = Add(result, term)
    return result


def supports(columns, target):
    """Column sets that a floating-point solver uses for target under a few objectives; empty when it finds none."""
    import numpy
    from scipy.optimize import linprog
    rows = sorted({m for column in columns for m in column} | set(target))
    index = {row: i for i, row in enumerate(rows)}
    matrix = numpy.zeros((len(rows), len(columns)))
    for j, column in enumerate(columns):
        for m, c in column.items():
            matrix[index[m], j] = float(c)
    vector = numpy.array([float(target.get(row, 0)) for row in rows])
    sizes = numpy.array([float(sum(len(str(c)) for c in column.values())) for column in columns])
    random = numpy.random.default_rng(len(columns))
    found = []
    for objective in [numpy.ones(len(columns)), sizes, numpy.zeros(len(columns))] + [random.random(len(columns)) for _ in range(3)]:
        result = linprog(objective, A_eq=matrix, b_eq=vector, bounds=(0, None), method="highs")
        if result.status != 0:
            return found
        chosen = [j for j, w in enumerate(result.x) if w > 1e-9]
        if chosen not in found:
            found.append(chosen)
    return found


def size(weights):
    return max([w.numerator for w in weights if w] + [lcm(w.denominator for w in weights)])


def feasible(columns, target):
    """Nonnegative rational weights for columns summing to target, preferring small numbers when a fast solver is installed."""
    try:
        candidates = supports(columns, target)
    except ImportError:
        return exact_feasible(columns, target)
    best = None
    for chosen in candidates:
        weights = exact_feasible([columns[j] for j in chosen], target)
        if weights is None:
            continue
        full = [Fraction(0)] * len(columns)
        for j, w in zip(chosen, weights):
            full[j] = w
        if best is None or size(full) < size(best):
            best = full
    return best


def exact_feasible(columns, target):
    """Exact phase-one simplex: nonnegative weights for columns summing to target."""
    rows = sorted({m for column in columns for m in column} | set(target))
    count = len(columns)
    table = []
    for row in rows:
        sign = -1 if target.get(row, 0) < 0 else 1
        table.append([sign * column.get(row, Fraction(0)) for column in columns] +
                     [Fraction(1) if r == row else Fraction(0) for r in rows] +
                     [sign * target.get(row, Fraction(0))])
    basis = [count + i for i in range(len(rows))]
    while True:
        artificial_rows = [i for i, b in enumerate(basis) if b >= count]
        entering = next((j for j in range(count) if sum(table[i][j] for i in artificial_rows) > 0), None)
        if entering is None:
            break
        ratios = [(table[i][-1] / table[i][entering], basis[i], i)
                  for i in range(len(rows)) if table[i][entering] > 0]
        _, _, leaving = min(ratios)
        pivot = table[leaving][entering]
        table[leaving] = [value / pivot for value in table[leaving]]
        for i in range(len(rows)):
            if i != leaving and table[i][entering] != 0:
                factor = table[i][entering]
                table[i] = [a - factor * b for a, b in zip(table[i], table[leaving])]
        basis[leaving] = entering
    if any(basis[i] >= count and table[i][-1] != 0 for i in range(len(rows))):
        return None
    weights = [Fraction(0)] * count
    for i, b in enumerate(basis):
        if b < count:
            weights[b] = table[i][-1]
    return weights


def ranking(equation_polys, count):
    """Order variables so that a variable defined by an equation ranks above everything it is defined from."""
    defined = {}
    for e in equation_polys:
        for v in range(count):
            unit = tuple(1 if i == v else 0 for i in range(count))
            if v not in defined and unit in e and all(m == unit or m[v] == 0 for m in e):
                defined[v] = {i for m in e if m != unit for i, a in enumerate(m) if a}
                break
    order = []
    visiting = set()

    def visit(v):
        if v in order or v in visiting:
            return
        visiting.add(v)
        for w in sorted(defined.get(v, ())):
            visit(w)
        visiting.discard(v)
        order.append(v)
    for v in sorted(defined):
        visit(v)
    rest = [v for v in range(count) if v not in order]
    return list(reversed(rest[::-1] + order))


def monomial_key(rank):
    return lambda m: tuple(m[v] for v in rank)


def divides(lead, m):
    return all(a <= b for a, b in zip(lead, m))


def reduce(p, equation_polys, lead_monomials, key):
    """Divide p by the equations along a fixed lexicographic order; return the remainder and the quotients."""
    p = dict(p)
    remainder = {}
    quotients = [{} for _ in equation_polys]
    while p:
        m = max(p, key=key)
        j = next((j for j, lead in enumerate(lead_monomials) if divides(lead, m)), None)
        if j is None:
            remainder[m] = p.pop(m)
            continue
        factor = {tuple(a - b for a, b in zip(m, lead_monomials[j])): p[m] / equation_polys[j][lead_monomials[j]]}
        quotients[j] = add(quotients[j], factor)
        p = add(p, {k: -v for k, v in mul(factor, equation_polys[j]).items()})
    return remainder, quotients


def scaled(multipliers, factor):
    return {j: mul(factor, p) for j, p in multipliers.items()}


def summed(left, right):
    out = dict(left)
    for j, p in right.items():
        out[j] = add(out.get(j, {}), p)
    return out


def basis_of(equation_polys, key):
    """A Groebner basis of the equations along `key`, each element with the multipliers of the equations that give it."""
    elements = [(e, {j: {tuple(0 for _ in next(iter(e))): Fraction(1)}}) for j, e in enumerate(equation_polys) if e]
    pairs = list(itertools.combinations(range(len(elements)), 2))
    while pairs:
        (f, from_f), (g, from_g) = (elements[i] for i in pairs.pop())
        lead_f, lead_g = max(f, key=key), max(g, key=key)
        if not any(a and b for a, b in zip(lead_f, lead_g)):
            continue
        common = tuple(max(a, b) for a, b in zip(lead_f, lead_g))
        factor_f = {tuple(a - b for a, b in zip(common, lead_f)): 1 / f[lead_f]}
        factor_g = {tuple(a - b for a, b in zip(common, lead_g)): -1 / g[lead_g]}
        polys = [p for p, _ in elements]
        remainder, quotients = reduce(add(mul(factor_f, f), mul(factor_g, g)), polys, [max(p, key=key) for p in polys], key)
        if remainder:
            origin = summed(scaled(from_f, factor_f), scaled(from_g, factor_g))
            for (_, from_element), quotient in zip(elements, quotients):
                origin = summed(origin, scaled(from_element, {m: -c for m, c in quotient.items()}))
            pairs += [(i, len(elements)) for i in range(len(elements))]
            elements.append((remainder, origin))
    return elements


class Product:
    """A product of facts times a square, expanded only when needed."""

    def __init__(self, fact_polys, square_polys, chosen, k):
        self.parts = (fact_polys, square_polys, chosen, k)
        self.value = None

    def items(self):
        if self.value is None:
            fact_polys, square_polys, chosen, k = self.parts
            p = mul(square_polys[k], square_polys[k])
            for index in chosen:
                p = mul(p, fact_polys[index])
            self.value = p
        return self.value.items()


def candidates_of(fact_polys, square_polys, products):
    out = []
    for size in range(products + 1):
        for chosen in itertools.combinations_with_replacement(range(len(fact_polys)), size):
            for k, square in enumerate(square_polys):
                if size + (k > 0) > products:
                    continue
                out.append((chosen, k, Product(fact_polys, square_polys, chosen, k)))
    return out


def lcm(values):
    out = 1
    for v in values:
        out = out * v // math.gcd(out, v)
    return out


def reduced_search(count, fact_polys, square_polys, equation_polys, goal_poly, products):
    key = monomial_key(ranking(equation_polys, count))
    basis = basis_of(equation_polys, key)
    basis_polys = [p for p, _ in basis]
    lead_monomials = [max(p, key=key) for p in basis_polys]
    normal = lambda p: reduce(p, basis_polys, lead_monomials, key)[0]
    goal_form = normal(goal_poly)
    fact_forms = [normal(f) for f in fact_polys]
    square_forms = [normal(mul(q, q)) for q in square_polys]
    candidates = candidates_of(fact_polys, square_polys, products)
    forms = []
    for chosen, k, _ in candidates:
        form = square_forms[k]
        for index in chosen:
            form = normal(mul(form, fact_forms[index]))
        forms.append(form)
    weights = feasible(forms, goal_form)
    if weights is None:
        return None
    scale = lcm(w.denominator for w in weights)
    residual = {m: scale * c for m, c in goal_poly.items()}
    terms = []
    for (chosen, k, p), weight in zip(candidates, weights):
        if weight:
            integer = weight * scale
            terms.append((integer, chosen, k))
            residual = add(residual, {m: -integer * c for m, c in p.items()})
    remainder, quotients = reduce(residual, basis_polys, lead_monomials, key)
    if remainder:
        return None
    multipliers = {}
    for (_, origin), quotient in zip(basis, quotients):
        multipliers = summed(multipliers, scaled(origin, quotient))
    multipliers = {j: q for j, q in multipliers.items() if q}
    extra_scale = lcm(c.denominator for q in multipliers.values() for c in q.values())
    terms = [(int(c * extra_scale), chosen, k) for c, chosen, k in terms]
    multipliers = {j: {m: c * extra_scale for m, c in q.items()} for j, q in multipliers.items()}
    return scale * extra_scale, terms, multipliers


def expanded_search(count, fact_polys, square_polys, equation_polys, goal_poly, products, extra):
    candidates = [("product", chosen, k, dict(p.items())) for chosen, k, p in candidates_of(fact_polys, square_polys, products)]
    top = max([degree(c[3]) for c in candidates] + [degree(goal_poly)]) + extra
    for j, e in enumerate(equation_polys):
        for total in range(top - degree(e) + 1):
            for m in itertools.product(range(total + 1), repeat=count):
                if sum(m) != total:
                    continue
                shifted = mul({m: Fraction(1)}, e)
                candidates.append(("plus", j, m, shifted))
                candidates.append(("minus", j, m, {k: -v for k, v in shifted.items()}))
    weights = feasible([c[3] for c in candidates], goal_poly)
    if weights is None:
        return None
    scale = lcm(w.denominator for w in weights)
    terms = []
    multipliers = {}
    for candidate, weight in zip(candidates, weights):
        if weight == 0:
            continue
        integer = weight * scale
        if candidate[0] == "product":
            _, chosen, k, _ = candidate
            terms.append((int(integer), chosen, k))
        else:
            kind, j, m, _ = candidate
            sign = 1 if kind == "plus" else -1
            multipliers[j] = add(multipliers.get(j, {}), {m: sign * integer})
    return scale, terms, multipliers


def search(names, facts, equations, goal, squares, products, extra=0):
    count = len(names)
    fact_polys = [poly(parse(f, names), count) for f in facts]
    square_exprs = [Num(1)] + [parse(s, names) for s in squares]
    square_polys = [poly(e, count) for e in square_exprs]
    equation_polys = [poly(parse(e, names), count) for e in equations]
    goal_poly = poly(parse(goal, names), count)
    found = reduced_search(count, fact_polys, square_polys, equation_polys, goal_poly, products)
    if found is None and extra:
        found = expanded_search(count, fact_polys, square_polys, equation_polys, goal_poly, products, extra)
    if found is None:
        return None
    scale, terms, multipliers = found
    check = {}
    for coefficient, chosen, k in terms:
        p = mul(square_polys[k], square_polys[k])
        for index in chosen:
            p = mul(p, fact_polys[index])
        check = add(check, {m: coefficient * c for m, c in p.items()})
    for j, multiplier in multipliers.items():
        check = add(check, mul(multiplier, equation_polys[j]))
    assert check == {m: scale * c for m, c in goal_poly.items() if c}, "certificate does not reproduce the goal"
    terms = [(coefficient, chosen, square_exprs[k]) for coefficient, chosen, k in terms]
    return scale - 1, terms, {j: m for j, m in multipliers.items() if m}


def render(denominator, terms, multipliers):
    items = []
    for coefficient, chosen, square in terms:
        indices = "C.NoIndices{}"
        for index in reversed(chosen):
            indices = f"C.MoreIndices{{{index}n, {indices}}}"
        items.append(f"C.Product{{{coefficient}n, {indices}, {bend(square)}}}")
    for j, multiplier in sorted(multipliers.items()):
        items.append(f"C.Multiple{{{j}n, {bend(poly_expr(multiplier))}}}")
    text = "C.NoTerms{}"
    for item in reversed(items):
        text = f"C.MoreTerms{{{item}, {text}}}"
    return f"{denominator}n", text


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("problem", help="JSON file with names, facts, equations, goal and optional squares")
    parser.add_argument("--products", type=int, default=2, help="largest number of factors in one term")
    parser.add_argument("--extra-degree", type=int, default=1,
                        help="how far equation multiples may exceed the degree of the goal and the products")
    arguments = parser.parse_args()
    with open(arguments.problem) as file:
        problem = json.load(file)
    names = problem["names"]
    found = search(names, problem.get("facts", []), problem.get("equations", []), problem["goal"],
                   problem.get("squares", []), arguments.products, arguments.extra_degree)
    if found is None:
        sys.exit("no certificate with these facts, equations and squares")
    denominator, terms = render(*found)
    print("denominator:", denominator)
    print("terms:", terms)
    print("goal:", bend(parse(problem["goal"], names)))
    for kind in ("facts", "equations"):
        for text in problem.get(kind, []):
            print(f"{kind[:-1]}:", bend(parse(text, names)))


if __name__ == "__main__":
    main()
