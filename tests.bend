import Base
import ./num.bend as N
import ./linreg.bend as L

# Test runner: prints PASS/FAIL per case and the count.
# Run: bend tests.bend
# Expected values were computed with Python's fractions.Fraction.

# Building numbers
# ----------------

# n
def ri(+n: Nat) -> N.Rat:
  N.Rat{N.Pos{n}, 0n}

# -n
def rn(+n: Nat) -> N.Rat:
  N.Rat{N.Int.minus(n), 0n}

# n / d, d >= 1
def rq(+n: Nat, +d: Nat) -> N.Rat:
  N.Rat.reduce(N.Pos{n}, Nat.sub(d, 1n))

# -n / d, d >= 1
def rqn(+n: Nat, +d: Nat) -> N.Rat:
  N.Rat.reduce(N.Int.minus(n), Nat.sub(d, 1n))

# Comparing results
# -----------------

def req(a: N.Rat, b: N.Rat) -> Bool:
  N.Rat.is_eq(a, b)

def list_eq(xs: +List<N.Rat>, ys: +List<N.Rat>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, xt} Con{y, yt}:
      Bool.and(req(x, y), list_eq(xt, yt))
    case _ _:
      False{}

def code(e: L.FitError) -> Nat:
  match e:
    case L.Empty{}:
      0n
    case L.LengthMismatch{}:
      1n
    case L.Degenerate{}:
      2n
    case L.TooLarge{}:
      3n

def fit_is(r: Result<L.FitError, L.LinearRegression>, a: N.Rat, b: N.Rat) -> Bool:
  match r:
    case Done{L.LinearRegression{fi, c, i}}:
      Bool.and(req(c, a), req(i, b))
    case Fail{e}:
      False{}

def fit_fails(r: Result<L.FitError, L.LinearRegression>, +c: Nat) -> Bool:
  match r:
    case Done{m}:
      False{}
    case Fail{e}:
      Nat.is_eq(code(e), c)

def pred_is(r: Result<L.FitError, +List<N.Rat>>, ys: +List<N.Rat>) -> Bool:
  match r:
    case Done{ps}:
      list_eq(ps, ys)
    case Fail{e}:
      False{}

def pred_fails(r: Result<L.FitError, +List<N.Rat>>, +c: Nat) -> Bool:
  match r:
    case Done{ps}:
      False{}
    case Fail{e}:
      Nat.is_eq(code(e), c)

def score_is(r: Result<L.FitError, N.Rat>, v: N.Rat) -> Bool:
  match r:
    case Done{s}:
      req(s, v)
    case Fail{e}:
      False{}

def score_fails(r: Result<L.FitError, N.Rat>, +c: Nat) -> Bool:
  match r:
    case Done{s}:
      False{}
    case Fail{e}:
      Nat.is_eq(code(e), c)

def model(r: Result<L.FitError, L.LinearRegression>) -> L.LinearRegression:
  match r:
    case Done{m}:
      m
    case Fail{e}:
      L.LinearRegression{True{}, N.Rat.zero(), N.Rat.zero()}

def stats_eq(a: L.Stats, b: L.Stats) -> Bool:
  match a b:
    case L.Stats{n1, x1, y1, xy1, xx1} L.Stats{n2, x2, y2, xy2, xx2}:
      Bool.and(N.Int.is_eq(n1, n2), Bool.and(N.Int.is_eq(x1, x2), Bool.and(N.Int.is_eq(y1, y2),
        Bool.and(N.Int.is_eq(xy1, xy2), N.Int.is_eq(xx1, xx2)))))

# n points with small pseudo-random integer coordinates (fixed seed)
def gen(n: Nat, +seed: Nat) -> +List<L.Point>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      +s1 = Nat.mod(Nat.add(Nat.mul(seed, 75n), 74n), 65537n)
      +s2 = Nat.mod(Nat.add(Nat.mul(s1, 75n), 74n), 65537n)
      L.Pt{N.Rat{N.Int.sub_nat(Nat.mod(s1, 19n), 9n), 0n}, N.Rat{N.Int.sub_nat(Nat.mod(s2, 19n), 9n), 0n}} <> gen(m, s2)

def is_3_4(r: N.Rat) -> Bool:
  match r:
    case N.Rat{N.Pos{3n}, 3n}:
      True{}
    case _:
      False{}

def is_none(m: Maybe<N.Rat>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{q}:
      False{}

# Cases
# -----

def c1x() -> +List<N.Rat>:
  [ri(1n), ri(2n), ri(3n)]

def c1y() -> +List<N.Rat>:
  [ri(2n), ri(4n), ri(7n)]

def cases() -> List<(String & Bool)>:
  [("Rat: 1/2 + 1/3 == 5/6", req(N.Rat.add(rq(1n, 2n), rq(1n, 3n)), rq(5n, 6n))),
   ("Rat: lowest terms, 6/8 is Rat{3, 3}", is_3_4(N.Rat.reduce(N.Pos{6n}, 7n))),
   ("Rat: division by zero is None", is_none(N.Rat.div(ri(1n), N.Rat.zero()))),
   ("Rat: -1/2 * 2/3 == -1/3", req(N.Rat.mul(rqn(1n, 2n), rq(2n, 3n)), rqn(1n, 3n))),
   ("fit [1,2,3] -> [2,4,7]: coef 5/2, intercept -2/3", fit_is(L.LinearRegression.fit(True{}, c1x(), c1y()), rq(5n, 2n), rqn(2n, 3n))),
   ("fit exact line y = 2x + 1", fit_is(L.LinearRegression.fit(True{}, [ri(0n), ri(1n), ri(2n), ri(3n)], [ri(1n), ri(3n), ri(5n), ri(7n)]), ri(2n), ri(1n))),
   ("fit fractions: coef 1/2, intercept 1/36",
     fit_is(L.LinearRegression.fit(True{}, [rq(1n, 2n), rq(3n, 2n), rq(5n, 2n)], [rq(1n, 3n), rq(2n, 3n), rq(4n, 3n)]), rq(1n, 2n), rq(1n, 36n))),
   ("fit negatives [-1,0,1] -> [1,0,1]: coef 0, intercept 2/3",
     fit_is(L.LinearRegression.fit(True{}, [rn(1n), ri(0n), ri(1n)], [ri(1n), ri(0n), ri(1n)]), ri(0n), rq(2n, 3n))),
   ("fit through the origin: coef 31/14, intercept 0", fit_is(L.LinearRegression.fit(False{}, c1x(), c1y()), rq(31n, 14n), ri(0n))),
   ("fit: every x equal is Degenerate", fit_fails(L.LinearRegression.fit(True{}, [ri(2n), ri(2n), ri(2n)], [ri(1n), ri(2n), ri(3n)]), 2n)),
   ("fit: one point is Degenerate", fit_fails(L.LinearRegression.fit(True{}, [ri(2n)], [ri(1n)]), 2n)),
   ("fit origin: every x zero is Degenerate", fit_fails(L.LinearRegression.fit(False{}, [ri(0n), ri(0n)], [ri(1n), ri(2n)]), 2n)),
   ("fit origin: one nonzero point works", fit_is(L.LinearRegression.fit(False{}, [ri(2n)], [ri(3n)]), rq(3n, 2n), ri(0n))),
   ("fit: no points is Empty", fit_fails(L.LinearRegression.fit(True{}, [], []), 0n)),
   ("fit: lengths differ is LengthMismatch", fit_fails(L.LinearRegression.fit(True{}, [ri(1n), ri(2n)], [ri(1n)]), 1n)),
   ("fit: past the size limit is TooLarge", fit_fails(L.LinearRegression.fit(True{}, [ri(16777216n), ri(1n)], [ri(0n), ri(1n)]), 3n)),
   ("predict 5/2 x - 2/3 at [0, 1/2, -3]",
     pred_is(L.LinearRegression.predict(L.LinearRegression{True{}, rq(5n, 2n), rqn(2n, 3n)}, [ri(0n), rq(1n, 2n), rn(3n)]),
       [rqn(2n, 3n), rq(7n, 12n), rqn(49n, 6n)])),
   ("predict past the size limit is TooLarge",
     pred_fails(L.LinearRegression.predict(L.LinearRegression{True{}, ri(16777216n), ri(0n)}, [ri(16777216n)]), 3n)),
   ("score of the fitted [1,2,3] line is 75/76", score_is(L.LinearRegression.score(model(L.LinearRegression.fit(True{}, c1x(), c1y())), c1x(), c1y()), rq(75n, 76n))),
   ("score of an exact line is 1", score_is(L.LinearRegression.score(L.LinearRegression{True{}, ri(2n), ri(1n)}, [ri(0n), ri(1n), ri(2n)], [ri(1n), ri(3n), ri(5n)]), ri(1n))),
   ("score through the origin is 517/532", score_is(L.LinearRegression.score(model(L.LinearRegression.fit(False{}, c1x(), c1y())), c1x(), c1y()), rq(517n, 532n))),
   ("score: every y equal is Degenerate", score_fails(L.LinearRegression.score(L.LinearRegression{True{}, ri(1n), ri(0n)}, [ri(1n), ri(2n)], [ri(3n), ri(3n)]), 2n)),
   ("parallel sums == sequential sums (1000 points)", stats_eq(L.Stats.par(1n, gen(1000n, 7n)), L.Stats.seq(1n, gen(1000n, 7n))))]

# Report
# ------

def report.go(cases: List<(String & Bool)>, +passed: Nat, +total: Nat) -> String:
  match cases:
    case Nil{}:
      Nat.show(passed) ++ "/" ++ Nat.show(total) ++ " passed"
    case Con{(name, ok), t}:
      match ok:
        case True{}:
          "PASS " ++ name ++ "\n" ++ report.go(t, 1n+passed, 1n+total)
        case False{}:
          "FAIL " ++ name ++ "\n" ++ report.go(t, passed, 1n+total)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(report.go(cases(), 0n, 0n))
