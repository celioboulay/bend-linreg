import Base
import ./num.bend as N
import ./linreg.bend as L

# Laws for the exact number layer (num.bend) and phase A regression
# (linreg.bend). Each law is an open claim until PROOF.bend proves it.
# Bend's checker reasons about unbounded Nat; the runtime's 2^48 ceiling is
# handled by the size conditions below, under which fit and predict compute
# nothing above 2^47 (bounds argued in linreg.bend).

# Spec helpers
# ------------
# These fix what the laws mean. They use only Base's Nat, the constructors,
# and operations pinned down by the laws below, never the implementation's
# own gcd, predict or score.

# k divides n
def Divides(k: Nat, n: Nat) -> Type:
  &q: Nat -> {n == Nat.mul(k, q) : Nat}

def num(r: N.Rat) -> N.Int:
  match r:
    case N.Rat{n, d}:
      n

# the denominator, as a (positive) Int
def den(r: N.Rat) -> N.Int:
  match r:
    case N.Rat{n, d}:
      N.Pos{1n+d}

# r is in lowest terms: 1 is the only common divisor of |num| and den.
def Canon(r: N.Rat) -> Type:
  match r:
    case N.Rat{n, d}:
      @k: Nat -> Divides(k, N.Int.abs(n)) -> Divides(k, 1n+d) -> {k == 1n : Nat}

# r denotes n / d: num(r) * d == n * den(r)
def Denotes(+r: N.Rat, n: N.Int, d: N.Int) -> Type:
  {N.Int.mul(num(r), d) == N.Int.mul(n, den(r)) : N.Int}

# x and c denote the same number
def same(+x: N.Rat, +c: N.Rat) -> Bool:
  N.Int.is_eq(N.Int.mul(num(x), den(c)), N.Int.mul(num(c), den(x)))

# every x denotes the same number as c
def all_same(+c: N.Rat, xs: +List<N.Rat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, t}:
      Bool.and(same(x, c), all_same(c, t))

# the line's value a x + b
def at(a: N.Rat, b: N.Rat, x: N.Rat) -> N.Rat:
  N.Rat.add(N.Rat.mul(a, x), b)

def predict(+a: N.Rat, +b: N.Rat, xs: +List<N.Rat>) -> +List<N.Rat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      at(a, b, x) <> predict(a, b, t)

# Σ r_i, Σ x_i r_i and Σ r_i² for the residuals r_i = y_i - (a x_i + b).
# They walk xs and ys in pairs; the laws only use them on equal lengths.
def sum_r(+a: N.Rat, +b: N.Rat, xs: +List<N.Rat>, ys: +List<N.Rat>) -> N.Rat:
  match xs ys:
    case Con{x, xt} Con{y, yt}:
      N.Rat.add(N.Rat.sub(y, at(a, b, x)), sum_r(a, b, xt, yt))
    case _ _:
      N.Rat.zero()

def sum_xr(+a: N.Rat, +b: N.Rat, xs: +List<N.Rat>, ys: +List<N.Rat>) -> N.Rat:
  match xs ys:
    case Con{+x, xt} Con{y, yt}:
      N.Rat.add(N.Rat.mul(x, N.Rat.sub(y, at(a, b, x))), sum_xr(a, b, xt, yt))
    case _ _:
      N.Rat.zero()

def sse(+a: N.Rat, +b: N.Rat, xs: +List<N.Rat>, ys: +List<N.Rat>) -> N.Rat:
  match xs ys:
    case Con{x, xt} Con{y, yt}:
      +r = N.Rat.sub(y, at(a, b, x))
      N.Rat.add(N.Rat.mul(r, r), sse(a, b, xt, yt))
    case _ _:
      N.Rat.zero()

# The size limit (linreg.bend's header), restated with exact arithmetic:
# fit and predict must accept exactly the inputs these conditions allow.

def K() -> Nat:
  Nat.mul(16777216n, 8388608n)

def lcm(+a: Nat, +b: Nat) -> Nat:
  Nat.div(Nat.mul(a, b), N.Nat.gcd(a, b))

def dnat(r: N.Rat) -> Nat:
  match r:
    case N.Rat{n, d}:
      1n+d

# lcm of acc and every denominator in rs
def den_lcm(rs: +List<N.Rat>, +acc: Nat) -> Nat:
  match rs:
    case Nil{}:
      acc
    case Con{r, t}:
      den_lcm(t, lcm(acc, dnat(r)))

# the largest |r| l over rs
def mag(rs: +List<N.Rat>, +l: Nat) -> Nat:
  match rs:
    case Nil{}:
      0n
    case Con{+r, t}:
      Nat.max(Nat.mul(N.Int.abs(num(r)), Nat.div(l, dnat(r))), mag(t, l))

def fit_fits.go(+n: Nat, +l: Nat, +b: Nat) -> Bool:
  Bool.and(Nat.is_le(l, K()),
    Nat.is_le(Nat.mul(Nat.mul(Nat.mul(n, n), Nat.mul(b, b)), Nat.max(Nat.mul(2n, b), l)), K()))

# fit: L <= K and n² B² max(2B, L) <= K
def fit_fits(+xs: +List<N.Rat>, +ys: +List<N.Rat>) -> Bool:
  +l = den_lcm(ys, den_lcm(xs, 1n))
  fit_fits.go(List.length(&2, N.Rat, xs), l, Nat.max(mag(xs, l), mag(ys, l)))

# every x = u / v has max(|ca u| + |cb v|, d v) <= K
def predict_fits.xs(+ca: Nat, +cb: Nat, +d: Nat, xs: +List<N.Rat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      Bool.and(
        Nat.is_le(Nat.max(Nat.add(Nat.mul(ca, N.Int.abs(num(x))), Nat.mul(cb, dnat(x))), Nat.mul(d, dnat(x))), K()),
        predict_fits.xs(ca, cb, d, t))

def predict_fits.go(+p: Nat, +q: Nat, +r: Nat, +s: Nat, +d: Nat, xs: +List<N.Rat>) -> Bool:
  +ca = Nat.mul(p, Nat.div(d, q))
  +cb = Nat.mul(r, Nat.div(d, s))
  Bool.and(Nat.is_le(Nat.max(d, Nat.max(ca, cb)), K()), predict_fits.xs(ca, cb, d, xs))

# predict: with d = lcm(den a, den b), coef = ca / d and intercept = cb / d,
# max(|ca|, |cb|, d) <= K and every x passes predict_fits.xs
def predict_fits(+a: N.Rat, +b: N.Rat, xs: +List<N.Rat>) -> Bool:
  predict_fits.go(N.Int.abs(num(a)), dnat(a), N.Int.abs(num(b)), dnat(b), lcm(dnat(a), dnat(b)), xs)

# gcd
# ---

law Nat.gcd_dvd:
  for a: Nat
  for b: Nat
  Divides(N.Nat.gcd(a, b), a) & Divides(N.Nat.gcd(a, b), b)

law Nat.gcd_greatest:
  for k: Nat
  for a: Nat
  for b: Nat
  for ka: Divides(k, a)
  for kb: Divides(k, b)
  Divides(k, N.Nat.gcd(a, b))

# The fuel 1 + b is enough: any larger fuel gives the same answer, so the
# fuel-exhausted case is never what produces the result.
law Nat.gcd_fuel:
  for k: Nat
  for a: Nat
  for b: Nat
  {N.Nat.gcd.go(Nat.add(k, 1n+b), a, b) == N.Nat.gcd(a, b) : Nat}

# Int
# ---
# sub_nat(a, b) is a - b. The first three laws determine it, and every
# operation is pinned to Nat arithmetic on such differences (every Int is
# one: Pos{n} is n - 0, Neg{n} is 0 - (1 + n)).

law Int.sub_nat_zero:
  for a: Nat
  {N.Int.sub_nat(a, 0n) == N.Pos{a} : N.Int}

law Int.sub_nat_neg:
  for b: Nat
  {N.Int.sub_nat(0n, 1n+b) == N.Neg{b} : N.Int}

law Int.sub_nat_succ:
  for a: Nat
  for b: Nat
  {N.Int.sub_nat(1n+a, 1n+b) == N.Int.sub_nat(a, b) : N.Int}

law Int.neg_def:
  for a: Nat
  for b: Nat
  {N.Int.neg(N.Int.sub_nat(a, b)) == N.Int.sub_nat(b, a) : N.Int}

law Int.add_def:
  for a: Nat
  for b: Nat
  for c: Nat
  for d: Nat
  {N.Int.add(N.Int.sub_nat(a, b), N.Int.sub_nat(c, d))
    == N.Int.sub_nat(Nat.add(a, c), Nat.add(b, d)) : N.Int}

law Int.mul_def:
  for a: Nat
  for b: Nat
  for c: Nat
  for d: Nat
  {N.Int.mul(N.Int.sub_nat(a, b), N.Int.sub_nat(c, d))
    == N.Int.sub_nat(Nat.add(Nat.mul(a, c), Nat.mul(b, d)),
                     Nat.add(Nat.mul(a, d), Nat.mul(b, c))) : N.Int}

law Int.abs_def:
  for a: Nat
  for b: Nat
  {N.Int.abs(N.Int.sub_nat(a, b)) == Nat.add(Nat.sub(a, b), Nat.sub(b, a)) : Nat}

law Int.eq_def:
  for a: Nat
  for b: Nat
  for c: Nat
  for d: Nat
  {N.Int.is_eq(N.Int.sub_nat(a, b), N.Int.sub_nat(c, d))
    == Nat.is_eq(Nat.add(a, d), Nat.add(c, b)) : Bool}

law Int.le_def:
  for a: Nat
  for b: Nat
  for c: Nat
  for d: Nat
  {N.Int.is_le(N.Int.sub_nat(a, b), N.Int.sub_nat(c, d))
    == Nat.is_le(Nat.add(a, d), Nat.add(c, b)) : Bool}

# Ring laws, as used by the regression proofs.

law Int.add_comm:
  for a: N.Int
  for b: N.Int
  {N.Int.add(a, b) == N.Int.add(b, a) : N.Int}

law Int.add_assoc:
  for a: N.Int
  for b: N.Int
  for c: N.Int
  {N.Int.add(N.Int.add(a, b), c) == N.Int.add(a, N.Int.add(b, c)) : N.Int}

law Int.mul_comm:
  for a: N.Int
  for b: N.Int
  {N.Int.mul(a, b) == N.Int.mul(b, a) : N.Int}

law Int.mul_assoc:
  for a: N.Int
  for b: N.Int
  for c: N.Int
  {N.Int.mul(N.Int.mul(a, b), c) == N.Int.mul(a, N.Int.mul(b, c)) : N.Int}

law Int.mul_add:
  for a: N.Int
  for b: N.Int
  for c: N.Int
  {N.Int.mul(a, N.Int.add(b, c)) == N.Int.add(N.Int.mul(a, b), N.Int.mul(a, c)) : N.Int}

# Rat
# ---

law Rat.make_zero:
  for n: N.Int
  {N.Rat.make(n, N.Int.zero()) == None{} : Maybe<N.Rat>}

# Rat.make(n, d) is the canonical rational n / d.
law Rat.make_ok:
  for n: N.Int
  for d: N.Int
  for nz: {d != N.Int.zero() : N.Int}
  exs r: N.Rat
  {N.Rat.make(n, d) == Some{r} : Maybe<N.Rat>} & Canon(r) & Denotes(r, n, d)

# Structural equality on canonical Rats is equality of the numbers.
law Rat.canon_eq:
  for a: N.Rat
  for b: N.Rat
  for ca: Canon(a)
  for cb: Canon(b)
  for h: Denotes(a, num(b), den(b))
  {a == b : N.Rat}

# Every operation returns a canonical Rat denoting the right number.

law Rat.of_int_ok:
  for n: N.Int
  Canon(N.Rat.of_int(n)) & Denotes(N.Rat.of_int(n), n, N.Int.one())

law Rat.neg_ok:
  for a: N.Rat
  for ca: Canon(a)
  Canon(N.Rat.neg(a)) & Denotes(N.Rat.neg(a), N.Int.neg(num(a)), den(a))

law Rat.add_ok:
  for a: N.Rat
  for b: N.Rat
  Canon(N.Rat.add(a, b))
    & Denotes(N.Rat.add(a, b),
        N.Int.add(N.Int.mul(num(a), den(b)), N.Int.mul(num(b), den(a))),
        N.Int.mul(den(a), den(b)))

law Rat.sub_ok:
  for a: N.Rat
  for b: N.Rat
  Canon(N.Rat.sub(a, b))
    & Denotes(N.Rat.sub(a, b),
        N.Int.sub(N.Int.mul(num(a), den(b)), N.Int.mul(num(b), den(a))),
        N.Int.mul(den(a), den(b)))

law Rat.mul_ok:
  for a: N.Rat
  for b: N.Rat
  Canon(N.Rat.mul(a, b))
    & Denotes(N.Rat.mul(a, b), N.Int.mul(num(a), num(b)), N.Int.mul(den(a), den(b)))

law Rat.inv_zero:
  for d: Nat
  {N.Rat.inv(N.Rat{N.Pos{0n}, d}) == None{} : Maybe<N.Rat>}

law Rat.inv_ok:
  for a: N.Rat
  for ca: Canon(a)
  for nz: {num(a) != N.Int.zero() : N.Int}
  exs r: N.Rat
  {N.Rat.inv(a) == Some{r} : Maybe<N.Rat>} & Canon(r) & Denotes(r, den(a), num(a))

law Rat.div_zero:
  for a: N.Rat
  for d: Nat
  {N.Rat.div(a, N.Rat{N.Pos{0n}, d}) == None{} : Maybe<N.Rat>}

law Rat.div_ok:
  for a: N.Rat
  for b: N.Rat
  for nz: {num(b) != N.Int.zero() : N.Int}
  exs r: N.Rat
  {N.Rat.div(a, b) == Some{r} : Maybe<N.Rat>}
    & Canon(r)
    & Denotes(r, N.Int.mul(num(a), den(b)), N.Int.mul(den(a), num(b)))

law Rat.le_def:
  for a: N.Rat
  for b: N.Rat
  {N.Rat.is_le(a, b)
    == N.Int.is_le(N.Int.mul(num(a), den(b)), N.Int.mul(num(b), den(a))) : Bool}

# Field laws, as used by the regression proofs.

law Rat.add_comm:
  for a: N.Rat
  for b: N.Rat
  {N.Rat.add(a, b) == N.Rat.add(b, a) : N.Rat}

law Rat.add_assoc:
  for a: N.Rat
  for b: N.Rat
  for c: N.Rat
  {N.Rat.add(N.Rat.add(a, b), c) == N.Rat.add(a, N.Rat.add(b, c)) : N.Rat}

law Rat.add_zero:
  for a: N.Rat
  for ca: Canon(a)
  {N.Rat.add(a, N.Rat.zero()) == a : N.Rat}

law Rat.add_neg:
  for a: N.Rat
  {N.Rat.add(a, N.Rat.neg(a)) == N.Rat.zero() : N.Rat}

law Rat.mul_comm:
  for a: N.Rat
  for b: N.Rat
  {N.Rat.mul(a, b) == N.Rat.mul(b, a) : N.Rat}

law Rat.mul_assoc:
  for a: N.Rat
  for b: N.Rat
  for c: N.Rat
  {N.Rat.mul(N.Rat.mul(a, b), c) == N.Rat.mul(a, N.Rat.mul(b, c)) : N.Rat}

law Rat.mul_one:
  for a: N.Rat
  for ca: Canon(a)
  {N.Rat.mul(a, N.Rat.one()) == a : N.Rat}

law Rat.mul_add:
  for a: N.Rat
  for b: N.Rat
  for c: N.Rat
  {N.Rat.mul(a, N.Rat.add(b, c)) == N.Rat.add(N.Rat.mul(a, b), N.Rat.mul(a, c)) : N.Rat}

# Sums
# ----

# The parallel tree reduction equals the sequential fold, for every list.
law Stats.par_seq:
  for l: Nat
  for ps: +List<L.Point>
  {L.Stats.par(l, ps) == L.Stats.seq(l, ps) : L.Stats}

# Regression, phase A
# -------------------

law predict_ok:
  for fi: Bool
  for a: N.Rat
  for b: N.Rat
  for xs: +List<N.Rat>
  for small: {predict_fits(a, b, xs) == True{} : Bool}
  {L.LinearRegression.predict(L.LinearRegression{fi, a, b}, xs)
    == Done{predict(a, b, xs)} : Result<L.FitError, +List<N.Rat>>}

law predict_too_large:
  for fi: Bool
  for a: N.Rat
  for b: N.Rat
  for xs: +List<N.Rat>
  for big: {predict_fits(a, b, xs) == False{} : Bool}
  {L.LinearRegression.predict(L.LinearRegression{fi, a, b}, xs)
    == Fail{L.TooLarge{}} : Result<L.FitError, +List<N.Rat>>}

# fit fails exactly in the degenerate or too-large cases.

law fit_mismatch:
  for fi: Bool
  for xs: +List<N.Rat>
  for ys: +List<N.Rat>
  for h: {Nat.is_eq(List.length(&2, N.Rat, xs), List.length(&2, N.Rat, ys)) == False{} : Bool}
  {L.LinearRegression.fit(fi, xs, ys) == Fail{L.LengthMismatch{}} : Result<L.FitError, L.LinearRegression>}

law fit_empty:
  for fi: Bool
  {L.LinearRegression.fit(fi, Nil{}, Nil{}) == Fail{L.Empty{}} : Result<L.FitError, L.LinearRegression>}

law fit_too_large:
  for fi: Bool
  for x: N.Rat
  for xt: +List<N.Rat>
  for y: N.Rat
  for yt: +List<N.Rat>
  for len: {List.length(&2, N.Rat, xt) == List.length(&2, N.Rat, yt) : Nat}
  for big: {fit_fits(x <> xt, y <> yt) == False{} : Bool}
  {L.LinearRegression.fit(fi, x <> xt, y <> yt) == Fail{L.TooLarge{}} : Result<L.FitError, L.LinearRegression>}

# With an intercept: every x equal (one point included) has no unique line...
law fit_flat:
  for x: N.Rat
  for xt: +List<N.Rat>
  for y: N.Rat
  for yt: +List<N.Rat>
  for len: {List.length(&2, N.Rat, xt) == List.length(&2, N.Rat, yt) : Nat}
  for small: {fit_fits(x <> xt, y <> yt) == True{} : Bool}
  for flat: {all_same(x, xt) == True{} : Bool}
  {L.LinearRegression.fit(True{}, x <> xt, y <> yt) == Fail{L.Degenerate{}} : Result<L.FitError, L.LinearRegression>}

# ...and two different x always give one.
law fit_ok:
  for x: N.Rat
  for xt: +List<N.Rat>
  for y: N.Rat
  for yt: +List<N.Rat>
  for len: {List.length(&2, N.Rat, xt) == List.length(&2, N.Rat, yt) : Nat}
  for small: {fit_fits(x <> xt, y <> yt) == True{} : Bool}
  for spread: {all_same(x, xt) == False{} : Bool}
  exs m: L.LinearRegression
  {L.LinearRegression.fit(True{}, x <> xt, y <> yt) == Done{m} : Result<L.FitError, L.LinearRegression>}

# Through the origin: every x zero has no unique line, one nonzero x gives one.
law fit_origin_flat:
  for x: N.Rat
  for xt: +List<N.Rat>
  for y: N.Rat
  for yt: +List<N.Rat>
  for len: {List.length(&2, N.Rat, xt) == List.length(&2, N.Rat, yt) : Nat}
  for small: {fit_fits(x <> xt, y <> yt) == True{} : Bool}
  for zero: {all_same(N.Rat.zero(), x <> xt) == True{} : Bool}
  {L.LinearRegression.fit(False{}, x <> xt, y <> yt) == Fail{L.Degenerate{}} : Result<L.FitError, L.LinearRegression>}

law fit_origin_ok:
  for x: N.Rat
  for xt: +List<N.Rat>
  for y: N.Rat
  for yt: +List<N.Rat>
  for len: {List.length(&2, N.Rat, xt) == List.length(&2, N.Rat, yt) : Nat}
  for small: {fit_fits(x <> xt, y <> yt) == True{} : Bool}
  for nonzero: {all_same(N.Rat.zero(), x <> xt) == False{} : Bool}
  exs m: L.LinearRegression
  {L.LinearRegression.fit(False{}, x <> xt, y <> yt) == Done{m} : Result<L.FitError, L.LinearRegression>}

# Normal equations: the residuals of a fitted line sum to 0 and are
# orthogonal to x.
law normal_eq:
  for xs: +List<N.Rat>
  for ys: +List<N.Rat>
  for a: N.Rat
  for b: N.Rat
  for ok: {L.LinearRegression.fit(True{}, xs, ys)
    == Done{L.LinearRegression{True{}, a, b}} : Result<L.FitError, L.LinearRegression>}
  {sum_r(a, b, xs, ys) == N.Rat.zero() : N.Rat} & {sum_xr(a, b, xs, ys) == N.Rat.zero() : N.Rat}

law normal_eq_origin:
  for xs: +List<N.Rat>
  for ys: +List<N.Rat>
  for a: N.Rat
  for b: N.Rat
  for ok: {L.LinearRegression.fit(False{}, xs, ys)
    == Done{L.LinearRegression{False{}, a, b}} : Result<L.FitError, L.LinearRegression>}
  {b == N.Rat.zero() : N.Rat} & {sum_xr(a, b, xs, ys) == N.Rat.zero() : N.Rat}

# Least squares: no other line has a smaller sum of squared residuals.
law least_squares:
  for xs: +List<N.Rat>
  for ys: +List<N.Rat>
  for a: N.Rat
  for b: N.Rat
  for ok: {L.LinearRegression.fit(True{}, xs, ys)
    == Done{L.LinearRegression{True{}, a, b}} : Result<L.FitError, L.LinearRegression>}
  for a2: N.Rat
  for b2: N.Rat
  {N.Rat.is_le(sse(a, b, xs, ys), sse(a2, b2, xs, ys)) == True{} : Bool}

law least_squares_origin:
  for xs: +List<N.Rat>
  for ys: +List<N.Rat>
  for a: N.Rat
  for b: N.Rat
  for ok: {L.LinearRegression.fit(False{}, xs, ys)
    == Done{L.LinearRegression{False{}, a, b}} : Result<L.FitError, L.LinearRegression>}
  for a2: N.Rat
  {N.Rat.is_le(sse(a, b, xs, ys), sse(a2, N.Rat.zero(), xs, ys)) == True{} : Bool}
