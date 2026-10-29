import Base
import ./num.bend as N
import ./linreg.bend as L

# Benchmark: the parallel tree sum vs the sequential fold, and a full fit.
# Build: bend bench.bend -o bench
# Run:   ./bench <gen|seq|par|fit> +RTS --threads <k>
# Points are pseudo-random integers in [-9, 9] from a fixed seed.

# n points (fixed seed, small values)
def gen(n: Nat, +seed: Nat) -> +List<L.Point>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      +s1 = Nat.mod(Nat.add(Nat.mul(seed, 75n), 74n), 65537n)
      +s2 = Nat.mod(Nat.add(Nat.mul(s1, 75n), 74n), 65537n)
      L.Pt{N.Rat{N.Int.sub_nat(Nat.mod(s1, 19n), 9n), 0n}, N.Rat{N.Int.sub_nat(Nat.mod(s2, 19n), 9n), 0n}} <> gen(m, s2)

def xs_of(ps: +List<L.Point>) -> +List<N.Rat>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{L.Pt{x, y}, t}:
      x <> xs_of(t)

def ys_of(ps: +List<L.Point>) -> +List<N.Rat>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{L.Pt{x, y}, t}:
      y <> ys_of(t)

def show_stats(s: L.Stats) -> String:
  match s:
    case L.Stats{n, sx, sy, sxy, sxx}:
      "n=" ++ N.Int.show(n) ++ " Σx=" ++ N.Int.show(sx) ++ " Σy=" ++ N.Int.show(sy) ++ " Σxy=" ++ N.Int.show(sxy) ++ " Σx²=" ++ N.Int.show(sxx)

def show_fit(r: Result<L.FitError, L.LinearRegression>) -> String:
  match r:
    case Done{L.LinearRegression{fi, c, i}}:
      "coef=" ++ N.Rat.show(c) ++ " intercept=" ++ N.Rat.show(i)
    case Fail{e}:
      "fit failed"

def count(ps: +List<L.Point>) -> String:
  Nat.show(List.length(&2, L.Point, ps))

def fit_of(+ps: +List<L.Point>) -> String:
  show_fit(L.LinearRegression.fit(True{}, xs_of(ps), ys_of(ps)))

def run.go(seq: Bool, par: Bool, fit: Bool) -> String:
  match seq par fit:
    case True{} _ _:
      show_stats(L.Stats.seq(1n, gen(10000000n, 7n)))
    case False{} True{} _:
      show_stats(L.Stats.par(1n, gen(10000000n, 7n)))
    case False{} False{} True{}:
      fit_of(gen(300000n, 7n))
    case False{} False{} False{}:
      count(gen(10000000n, 7n))

def run(+m: String) -> String:
  run.go(String.eq(m, "seq"), String.eq(m, "par"), String.eq(m, "fit"))

def mode(args: List<String>) -> String:
  match args:
    case Con{p, Con{m, t}}:
      m
    case _:
      "par"

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    IO.print(run(mode(args)))
