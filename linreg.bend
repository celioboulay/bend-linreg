import Base
import ./num.bend as N

# Exact least-squares regression, phase A: one feature, closed form.
#
# Limitation: Bend's runtime aborts on a Nat past 2^48 - 1. fit, predict and
# score first measure their inputs, without overflowing, and answer TooLarge
# unless every value they compute is guaranteed to stay <= K = 2^47:
#   fit:     L <= K and n² B² max(2B, L) <= K
#   predict: W <= K and max(|a u| + |b v|, d v) <= K for every x = u / v
#   score:   W <= K, T <= K and 4 n² V² <= K
# n: number of points; L: lcm of the input denominators; B: largest |x L| or
# |y L|; d: lcm of the model's two denominators, with coef = a / d and
# intercept = b / d; W: max(|a|, |b|, d); T and V: see the Score section.

type FitError is Data:
  Empty{}
  LengthMismatch{}
  Degenerate{}
  TooLarge{}

# sklearn's LinearRegression, one feature: y = coef * x + intercept.
type LinearRegression is Data:
  LinearRegression{fit_intercept: Bool, coef: N.Rat, intercept: N.Rat}

type Point is Data:
  Pt{x: N.Rat, y: N.Rat}

def Point.zip(xs: +List<N.Rat>, ys: +List<N.Rat>) -> +List<Point>:
  match xs ys:
    case Con{x, xt} Con{y, yt}:
      Pt{x, y} <> Point.zip(xt, yt)
    case _ _:
      Nil{}

# Size limits
# -----------

# K = 2^47. The checks below take the limit as a parameter k, and fit,
# predict and score pass K; the laws hold for every k, which also keeps
# the checker (it counts in unary) from ever evaluating 2^47.
def Limit.k() -> Nat:
  Nat.mul(16777216n, 8388608n)

def Limit.ok(+k: Nat, +v: Nat) -> Bool:
  Nat.is_le(v, k)

def Limit.mul.go(+k: Nat, ok: Bool, +a: Nat, +b: Nat) -> Nat:
  match ok:
    case True{}:
      Nat.mul(a, b)
    case False{}:
      1n+k

# min(a b, K + 1), without overflow for a, b <= K + 1.
def Limit.mul(+k: Nat, +a: Nat, +b: Nat) -> Nat:
  match a:
    case 0n:
      0n
    case 1n+p:
      Limit.mul.go(k, Nat.is_le(b, Nat.div(k, a)), a, b)

def Limit.add.go(+k: Nat, ok: Bool, +a: Nat, +b: Nat) -> Nat:
  match ok:
    case True{}:
      Nat.add(a, b)
    case False{}:
      1n+k

# min(a + b, K + 1)
def Limit.add(+k: Nat, +a: Nat, +b: Nat) -> Nat:
  Limit.add.go(k, Nat.is_le(a, Nat.sub(k, b)), a, b)

# min(lcm(a, b), K + 1), for a, b >= 1
def Limit.lcm(+k: Nat, +a: Nat, +b: Nat) -> Nat:
  Limit.mul(k, Nat.div(a, N.Nat.gcd(a, b)), b)

# lcm of acc and every denominator in rs
def Limit.dens(+k: Nat, rs: +List<N.Rat>, +acc: Nat) -> Nat:
  match rs:
    case Nil{}:
      acc
    case Con{r, t}:
      Limit.dens(k, t, Limit.lcm(k, acc, N.Rat.den(r)))

# |r| l, an integer when den(r) divides l
def Limit.scaled(+k: Nat, +l: Nat, r: N.Rat) -> Nat:
  match r:
    case N.Rat{n, d}:
      Limit.mul(k, N.Int.abs(n), Nat.div(l, 1n+d))

# the largest |r| l over rs
def Limit.mag(+k: Nat, rs: +List<N.Rat>, +l: Nat) -> Nat:
  match rs:
    case Nil{}:
      0n
    case Con{r, t}:
      Nat.max(Limit.scaled(k, l, r), Limit.mag(k, t, l))

# fit's condition (bounds in LinearRegression.solve)
def Limit.fit(+k: Nat, +n: Nat, +l: Nat, +b: Nat) -> Bool:
  Bool.and(Limit.ok(k, l),
    Limit.ok(k, Limit.mul(k, Limit.mul(k, Limit.mul(k, n, n), Limit.mul(k, b, b)), Nat.max(Limit.mul(k, 2n, b), l))))

# Sums
# ----

# n, Σx, Σy, Σxy, Σx² over points scaled by a common denominator.
type Stats is Data:
  Stats{n: N.Int, sx: N.Int, sy: N.Int, sxy: N.Int, sxx: N.Int}

def Stats.zero() -> Stats:
  Stats{N.Pos{0n}, N.Pos{0n}, N.Pos{0n}, N.Pos{0n}, N.Pos{0n}}

def Stats.add(a: Stats, b: Stats) -> Stats:
  match a b:
    case Stats{n1, x1, y1, xy1, xx1} Stats{n2, x2, y2, xy2, xx2}:
      Stats{N.Int.add(n1, n2), N.Int.add(x1, x2), N.Int.add(y1, y2),
            N.Int.add(xy1, xy2), N.Int.add(xx1, xx2)}

# r * l as an integer, for l a multiple of r's denominator.
def Stats.scale(+l: Nat, r: N.Rat) -> N.Int:
  match r:
    case N.Rat{n, d}:
      N.Int.mul(n, N.Pos{Nat.div(l, 1n+d)})

def Stats.point.go(+x: N.Int, +y: N.Int) -> Stats:
  Stats{N.Pos{1n}, x, y, N.Int.mul(x, y), N.Int.mul(x, x)}

def Stats.point(+l: Nat, p: Point) -> Stats:
  match p:
    case Pt{x, y}:
      Stats.point.go(Stats.scale(l, x), Stats.scale(l, y))

# The reference: a plain sequential fold.
def Stats.seq(+l: Nat, ps: +List<Point>) -> Stats:
  match ps:
    case Nil{}:
      Stats.zero()
    case Con{p, t}:
      Stats.add(Stats.point(l, p), Stats.seq(l, t))

type Tree is Data:
  TNil{}
  TLeaf{p: Point}
  TNode{l: Tree, r: Tree}

def Tree.leaves(ps: +List<Point>) -> +List<Tree>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, t}:
      TLeaf{p} <> Tree.leaves(t)

# One round of pairing neighbours: [a, b, c] becomes [TNode{a, b}, c].
def Tree.pairs(ts: +List<Tree>) -> +List<Tree>:
  match ts:
    case Con{a, Con{b, t}}:
      TNode{a, b} <> Tree.pairs(t)
    case t:
      t

# Each round halves the list, so fuel = its length always ends with one tree.
def Tree.rounds(fuel: Nat, ts: +List<Tree>) -> +List<Tree>:
  match fuel:
    case 0n:
      ts
    case 1n+f:
      Tree.rounds(f, Tree.pairs(ts))

# Joins what is left (a single tree once fuel suffices) without dropping any.
def Tree.join(ts: +List<Tree>) -> Tree:
  match ts:
    case Nil{}:
      TNil{}
    case Con{t, Nil{}}:
      t
    case Con{t, r}:
      TNode{t, Tree.join(r)}

# A balanced tree holding every point of ps, in order.
def Tree.of_list(+n: Nat, ps: +List<Point>) -> Tree:
  Tree.join(Tree.rounds(n, Tree.leaves(ps)))

# Splits in two, recurses on both halves in parallel, combines.
def Tree.stats(+l: Nat, t: Tree) -> Stats:
  match t:
    case TNil{}:
      Stats.zero()
    case TLeaf{p}:
      Stats.point(l, p)
    case TNode{a, b}:
      sa sb = Tree.stats(l, a) Tree.stats(l, b)
      Stats.add(sa, sb)

def Stats.par(+l: Nat, +ps: +List<Point>) -> Stats:
  Tree.stats(l, Tree.of_list(List.length(&2, Point, ps), ps))

# Fit
# ---

def LinearRegression.done(fi: Bool, a: Maybe<N.Rat>, b: Maybe<N.Rat>) -> Result<FitError, LinearRegression>:
  match a b:
    case Some{a} Some{b}:
      Done{LinearRegression{fi, a, b}}
    case _ _:
      Fail{Degenerate{}}

# With intercept, on sums scaled by l, so |Σx|, |Σy| <= nB and |Σxy|, Σx² <= nB²:
#   D = nΣx² - (Σx)²                          0 <= D <= n²B²
#   coef = (nΣxy - ΣxΣy) / D                  numerator <= 2n²B²
#   intercept = (ΣyΣx² - ΣxΣxy) / (l D)       numerator <= 2n²B³, l D <= L n²B²
# D = 0 exactly when every x is equal.
def LinearRegression.solve(+l: Nat, s: Stats) -> Result<FitError, LinearRegression>:
  match s:
    case Stats{+n, +sx, +sy, +sxy, +sxx}:
      +d = N.Int.sub(N.Int.mul(n, sxx), N.Int.mul(sx, sx))
      LinearRegression.done(True{},
        N.Rat.make(N.Int.sub(N.Int.mul(n, sxy), N.Int.mul(sx, sy)), d),
        N.Rat.make(N.Int.sub(N.Int.mul(sy, sxx), N.Int.mul(sx, sxy)), N.Int.mul(N.Pos{l}, d)))

# Through the origin: coef = Σxy / Σx²; Σx² = 0 exactly when every x is 0.
def LinearRegression.solve_origin(s: Stats) -> Result<FitError, LinearRegression>:
  match s:
    case Stats{n, sx, sy, sxy, sxx}:
      LinearRegression.done(False{}, N.Rat.make(sxy, sxx), Some{N.Rat.zero()})

def LinearRegression.fit.stats(fit_intercept: Bool, +l: Nat, s: Stats) -> Result<FitError, LinearRegression>:
  match fit_intercept:
    case True{}:
      LinearRegression.solve(l, s)
    case False{}:
      LinearRegression.solve_origin(s)

def LinearRegression.fit.check(ok: Bool, fit_intercept: Bool, +l: Nat, xs: +List<N.Rat>, ys: +List<N.Rat>) -> Result<FitError, LinearRegression>:
  match ok:
    case False{}:
      Fail{TooLarge{}}
    case True{}:
      LinearRegression.fit.stats(fit_intercept, l, Stats.par(l, Point.zip(xs, ys)))

def LinearRegression.fit.data(+k: Nat, fit_intercept: Bool, xs: +List<N.Rat>, +ys: +List<N.Rat>) -> Result<FitError, LinearRegression>:
  match xs:
    case Nil{}:
      Fail{Empty{}}
    case Con{+x, +t}:
      +l = Limit.dens(k, ys, Limit.dens(k, x <> t, 1n))
      +b = Nat.max(Limit.mag(k, x <> t, l), Limit.mag(k, ys, l))
      LinearRegression.fit.check(Limit.fit(k, List.length(&2, N.Rat, ys), l, b), fit_intercept, l, x <> t, ys)

def LinearRegression.fit.sizes(+k: Nat, fit_intercept: Bool, same: Bool, xs: +List<N.Rat>, ys: +List<N.Rat>) -> Result<FitError, LinearRegression>:
  match same:
    case True{}:
      LinearRegression.fit.data(k, fit_intercept, xs, ys)
    case False{}:
      Fail{LengthMismatch{}}

# fit with the size limit k (the laws hold for every k)
def LinearRegression.fit.within(+k: Nat, fit_intercept: Bool, +xs: +List<N.Rat>, +ys: +List<N.Rat>) -> Result<FitError, LinearRegression>:
  LinearRegression.fit.sizes(k, fit_intercept,
    Nat.is_eq(List.length(&2, N.Rat, xs), List.length(&2, N.Rat, ys)), xs, ys)

# sklearn's LinearRegression(fit_intercept=...).fit(X, y), on one feature.
def LinearRegression.fit(fit_intercept: Bool, +xs: +List<N.Rat>, +ys: +List<N.Rat>) -> Result<FitError, LinearRegression>:
  LinearRegression.fit.within(Limit.k(), fit_intercept, xs, ys)

# Predict
# -------

# The model over one shared denominator d = lcm(den coef, den intercept):
# coef = a / d and intercept = b / d.
type Common is Data:
  Common{a: N.Int, b: N.Int, d: Nat}

def Common.of.go(p: N.Int, +q: Nat, r: N.Int, +s: Nat, +d: Nat) -> Common:
  Common{N.Int.mul(p, N.Pos{Nat.div(d, q)}), N.Int.mul(r, N.Pos{Nat.div(d, s)}), d}

def Common.of(m: LinearRegression) -> Common:
  match m:
    case LinearRegression{fi, N.Rat{p, +q}, N.Rat{r, +s}}:
      Common.of.go(p, 1n+q, r, 1n+s, N.Nat.lcm(1n+q, 1n+s))

# W = max(|a|, |b|, d) of Common.of(m), measured without overflow.
def Limit.common.go(+k: Nat, +p: Nat, +q: Nat, +r: Nat, +s: Nat, +d: Nat) -> Nat:
  Nat.max(d, Nat.max(Limit.mul(k, p, Nat.div(d, q)), Limit.mul(k, r, Nat.div(d, s))))

def Limit.common(+k: Nat, m: LinearRegression) -> Nat:
  match m:
    case LinearRegression{fi, N.Rat{p, +q}, N.Rat{r, +s}}:
      Limit.common.go(k, N.Int.abs(p), 1n+q, N.Int.abs(r), 1n+s, Limit.lcm(k, 1n+q, 1n+s))

# coef x + intercept for x = u / v is (a u + b v) / (d v).
def Common.at(c: Common, x: N.Rat) -> N.Rat:
  match c x:
    case Common{a, b, +d} N.Rat{u, +vp}:
      N.Rat.reduce(N.Int.add(N.Int.mul(a, u), N.Int.mul(b, N.Pos{1n+vp})), Nat.sub(Nat.mul(d, 1n+vp), 1n))

# Common.at's largest value: max(|a u| + |b v|, d v)
def Limit.at(+k: Nat, c: Common, x: N.Rat) -> Nat:
  match c x:
    case Common{a, b, +d} N.Rat{u, +vp}:
      Nat.max(Limit.add(k, Limit.mul(k, N.Int.abs(a), N.Int.abs(u)), Limit.mul(k, N.Int.abs(b), 1n+vp)),
              Limit.mul(k, d, 1n+vp))

def Limit.predict(+k: Nat, +c: Common, xs: +List<N.Rat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, t}:
      Nat.max(Limit.at(k, c, x), Limit.predict(k, c, t))

def LinearRegression.predict.go(+c: Common, xs: +List<N.Rat>) -> +List<N.Rat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Common.at(c, x) <> LinearRegression.predict.go(c, t)

def LinearRegression.predict.check(ok: Bool, +c: Common, xs: +List<N.Rat>) -> Result<FitError, +List<N.Rat>>:
  match ok:
    case False{}:
      Fail{TooLarge{}}
    case True{}:
      Done{LinearRegression.predict.go(c, xs)}

def LinearRegression.predict.model(+k: Nat, ok: Bool, m: LinearRegression, +xs: +List<N.Rat>) -> Result<FitError, +List<N.Rat>>:
  match ok:
    case False{}:
      Fail{TooLarge{}}
    case True{}:
      +c = Common.of(m)
      LinearRegression.predict.check(Limit.ok(k, Limit.predict(k, c, xs)), c, xs)

def LinearRegression.predict.within(+k: Nat, +m: LinearRegression, +xs: +List<N.Rat>) -> Result<FitError, +List<N.Rat>>:
  LinearRegression.predict.model(k, Limit.ok(k, Limit.common(k, m)), m, xs)

# coef x + intercept for every x.
def LinearRegression.predict(+m: LinearRegression, +xs: +List<N.Rat>) -> Result<FitError, +List<N.Rat>>:
  LinearRegression.predict.within(Limit.k(), m, xs)

# Score
# -----
# R² = 1 - SS_res / SS_tot, on integers. T is the lcm of every d v and every z
# (x = u / v, y = w / z), so each prediction and target scales to an integer:
#   P = (a u + b v) (T / (d v))  and  Y = w (T / z),
# and R² = (S - n Σ(Y - P)²) / S where S = nΣY² - (ΣY)² = n SS_tot T².

def Common.d(c: Common) -> Nat:
  match c:
    case Common{a, b, d}:
      d

# lcm of acc, every d v and every z, without overflow
def Limit.score_den(+k: Nat, xs: +List<N.Rat>, ys: +List<N.Rat>, +d: Nat, +acc: Nat) -> Nat:
  match xs ys:
    case Con{x, xt} Con{y, yt}:
      Limit.score_den(k, xt, yt, d, Limit.lcm(k, Limit.lcm(k, acc, Limit.mul(k, d, N.Rat.den(x))), N.Rat.den(y)))
    case _ _:
      acc

# The largest value computing P and Y takes for one point. With V the
# largest over all points, every value score computes is <= 4n²V².
def Limit.score_point(+k: Nat, c: Common, +t: Nat, x: N.Rat, y: N.Rat) -> Nat:
  match c x y:
    case Common{a, b, d} N.Rat{u, +vp} N.Rat{w, zp}:
      Nat.max(
        Limit.mul(k, Limit.add(k, Limit.mul(k, N.Int.abs(a), N.Int.abs(u)), Limit.mul(k, N.Int.abs(b), 1n+vp)),
                  Nat.div(t, Limit.mul(k, d, 1n+vp))),
        Limit.mul(k, N.Int.abs(w), Nat.div(t, 1n+zp)))

def Limit.score(+k: Nat, +c: Common, +t: Nat, xs: +List<N.Rat>, ys: +List<N.Rat>) -> Nat:
  match xs ys:
    case Con{x, xt} Con{y, yt}:
      Nat.max(Limit.score_point(k, c, t, x, y), Limit.score(k, c, t, xt, yt))
    case _ _:
      0n

# Σ Y, Σ Y², Σ (Y - P)²
type Sums is Data:
  Sums{sy: N.Int, syy: N.Int, srr: N.Int}

def Sums.point.go(+y: N.Int, p: N.Int) -> Sums:
  +r = N.Int.sub(y, p)
  Sums{y, N.Int.mul(y, y), N.Int.mul(r, r)}

def Sums.point(c: Common, +t: Nat, x: N.Rat, y: N.Rat) -> Sums:
  match c x y:
    case Common{a, b, d} N.Rat{u, +vp} N.Rat{w, zp}:
      Sums.point.go(
        N.Int.mul(w, N.Pos{Nat.div(t, 1n+zp)}),
        N.Int.mul(N.Int.add(N.Int.mul(a, u), N.Int.mul(b, N.Pos{1n+vp})),
                  N.Pos{Nat.div(t, Nat.mul(d, 1n+vp))}))

def Sums.add(s: Sums, t: Sums) -> Sums:
  match s t:
    case Sums{y1, yy1, rr1} Sums{y2, yy2, rr2}:
      Sums{N.Int.add(y1, y2), N.Int.add(yy1, yy2), N.Int.add(rr1, rr2)}

def Sums.of(+c: Common, +t: Nat, xs: +List<N.Rat>, ys: +List<N.Rat>) -> Sums:
  match xs ys:
    case Con{x, xt} Con{y, yt}:
      Sums.add(Sums.point(c, t, x, y), Sums.of(c, t, xt, yt))
    case _ _:
      Sums{N.Pos{0n}, N.Pos{0n}, N.Pos{0n}}

def LinearRegression.score.ratio(r: Maybe<N.Rat>) -> Result<FitError, N.Rat>:
  match r:
    case None{}:
      Fail{Degenerate{}}
    case Some{q}:
      Done{q}

def LinearRegression.score.finish(+n: N.Int, s: Sums) -> Result<FitError, N.Rat>:
  match s:
    case Sums{+sy, syy, srr}:
      +t = N.Int.sub(N.Int.mul(n, syy), N.Int.mul(sy, sy))
      LinearRegression.score.ratio(N.Rat.make(N.Int.sub(t, N.Int.mul(n, srr)), t))

def LinearRegression.score.check(ok: Bool, +n: Nat, +c: Common, +t: Nat, xs: +List<N.Rat>, ys: +List<N.Rat>) -> Result<FitError, N.Rat>:
  match ok:
    case False{}:
      Fail{TooLarge{}}
    case True{}:
      LinearRegression.score.finish(N.Pos{n}, Sums.of(c, t, xs, ys))

def LinearRegression.score.model(+k: Nat, ok: Bool, m: LinearRegression, +n: Nat, +xs: +List<N.Rat>, +ys: +List<N.Rat>) -> Result<FitError, N.Rat>:
  match ok:
    case False{}:
      Fail{TooLarge{}}
    case True{}:
      +c = Common.of(m)
      +t = Limit.score_den(k, xs, ys, Common.d(c), 1n)
      +v = Limit.score(k, c, t, xs, ys)
      LinearRegression.score.check(
        Bool.and(Limit.ok(k, t), Limit.ok(k, Limit.mul(k, Limit.mul(k, 4n, Limit.mul(k, n, n)), Limit.mul(k, v, v)))),
        n, c, t, xs, ys)

def LinearRegression.score.data(+k: Nat, +m: LinearRegression, xs: +List<N.Rat>, +ys: +List<N.Rat>) -> Result<FitError, N.Rat>:
  match xs:
    case Nil{}:
      Fail{Empty{}}
    case Con{+x, +t}:
      LinearRegression.score.model(k, Limit.ok(k, Limit.common(k, m)), m, List.length(&2, N.Rat, ys), x <> t, ys)

def LinearRegression.score.sizes(+k: Nat, +m: LinearRegression, same: Bool, xs: +List<N.Rat>, ys: +List<N.Rat>) -> Result<FitError, N.Rat>:
  match same:
    case False{}:
      Fail{LengthMismatch{}}
    case True{}:
      LinearRegression.score.data(k, m, xs, ys)

def LinearRegression.score.within(+k: Nat, +m: LinearRegression, +xs: +List<N.Rat>, +ys: +List<N.Rat>) -> Result<FitError, N.Rat>:
  LinearRegression.score.sizes(k, m, Nat.is_eq(List.length(&2, N.Rat, xs), List.length(&2, N.Rat, ys)), xs, ys)

# sklearn's score: R² = 1 - SS_res / SS_tot. Degenerate when every y is equal.
def LinearRegression.score(+m: LinearRegression, +xs: +List<N.Rat>, +ys: +List<N.Rat>) -> Result<FitError, N.Rat>:
  LinearRegression.score.within(Limit.k(), m, xs, ys)
