import Base
import ./num.bend as N
import ./linreg.bend as L

# Demo: fit, predict and score on a small dataset, all exact.
# Run: bend demo.bend

def q(+n: Nat, +d: Nat) -> N.Rat:
  N.Rat.reduce(N.Pos{n}, Nat.sub(d, 1n))

def xs() -> +List<N.Rat>:
  [q(1n, 1n), q(2n, 1n), q(3n, 1n), q(4n, 1n), q(5n, 1n)]

def ys() -> +List<N.Rat>:
  [q(21n, 10n), q(39n, 10n), q(62n, 10n), q(78n, 10n), q(101n, 10n)]

def show_list(rs: +List<N.Rat>) -> String:
  match rs:
    case Nil{}:
      ""
    case Con{r, Nil{}}:
      N.Rat.show(r)
    case Con{r, t}:
      N.Rat.show(r) ++ ", " ++ show_list(t)

def show_err(e: L.FitError) -> String:
  match e:
    case L.Empty{}:
      "Empty"
    case L.LengthMismatch{}:
      "LengthMismatch"
    case L.Degenerate{}:
      "Degenerate"
    case L.TooLarge{}:
      "TooLarge"

def show_pred(r: Result<L.FitError, +List<N.Rat>>) -> String:
  match r:
    case Done{ps}:
      "[" ++ show_list(ps) ++ "]"
    case Fail{e}:
      show_err(e)

def show_score(r: Result<L.FitError, N.Rat>) -> String:
  match r:
    case Done{s}:
      N.Rat.show(s)
    case Fail{e}:
      show_err(e)

def report(+fi: Bool, r: Result<L.FitError, L.LinearRegression>) -> String:
  match r:
    case Fail{e}:
      "fit failed: " ++ show_err(e)
    case Done{+m}:
      match m:
        case L.LinearRegression{f, c, i}:
          "coef      = " ++ N.Rat.show(c) ++ "\n" ++
          "intercept = " ++ N.Rat.show(i) ++ "\n" ++
          "predict([0, 6, 1/2]) = " ++ show_pred(L.LinearRegression.predict(m, [q(0n, 1n), q(6n, 1n), q(1n, 2n)])) ++ "\n" ++
          "score (R²) = " ++ show_score(L.LinearRegression.score(m, xs(), ys()))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("x = [" ++ show_list(xs()) ++ "]")
    IO.print("y = [" ++ show_list(ys()) ++ "]")
    IO.print("")
    IO.print("LinearRegression(fit_intercept=True)")
    IO.print(report(True{}, L.LinearRegression.fit(True{}, xs(), ys())))
    IO.print("")
    IO.print("LinearRegression(fit_intercept=False)")
    IO.print(report(False{}, L.LinearRegression.fit(False{}, xs(), ys())))
    IO.print("")
    IO.print("x all equal: " ++ report(True{}, L.LinearRegression.fit(True{}, [q(1n, 1n), q(1n, 1n)], [q(1n, 1n), q(2n, 1n)])))
