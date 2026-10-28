import Base

# Exact numbers: Int and Rat. Runtime arithmetic goes through Base's Nat
# operations, which are native; a Nat past 2^48-1 aborts rather than wraps.

# Nat helpers
# -----------

# Euclid's algorithm. b strictly decreases at each step, so fuel 1 + b
# always suffices; the 0n fuel case is never reached from Nat.gcd.
def Nat.gcd.go(fuel: Nat, a: Nat, +b: Nat) -> Nat:
  match fuel:
    case 0n:
      a
    case 1n+f:
      match b:
        case 0n:
          a
        case 1n+bp:
          Nat.gcd.go(f, b, Nat.mod(a, b))

def Nat.gcd(a: Nat, +b: Nat) -> Nat:
  Nat.gcd.go(1n+b, a, b)

def Nat.lcm(+a: Nat, +b: Nat) -> Nat:
  Nat.mul(Nat.div(a, Nat.gcd(a, b)), b)

# (1 + a) * (1 + b) - 1, written so that 1n+Nat.mul_pred(a, b) computes to
# Nat.mul(1n+a, 1n+b): denominators stay visibly positive.
def Nat.mul_pred(a: Nat, +b: Nat) -> Nat:
  Nat.add(b, Nat.mul(a, 1n+b))

# Int
# ---

# One representation per value: Pos{n} is n and Neg{n} is -(n + 1),
# so zero is only Pos{0n}.
type Int is Data:
  Pos{n: Nat}
  Neg{n: Nat}

def Int.zero() -> Int:
  Pos{0n}

def Int.one() -> Int:
  Pos{1n}

# -n
def Int.minus(n: Nat) -> Int:
  match n:
    case 0n:
      Pos{0n}
    case 1n+p:
      Neg{p}

def Int.sub_nat.go(lt: Bool, +a: Nat, +b: Nat) -> Int:
  match lt:
    case True{}:
      Neg{Nat.sub(b, 1n+a)}
    case False{}:
      Pos{Nat.sub(a, b)}

# a - b
def Int.sub_nat(+a: Nat, +b: Nat) -> Int:
  Int.sub_nat.go(Nat.is_lt(a, b), a, b)

def Int.neg(a: Int) -> Int:
  match a:
    case Pos{n}:
      Int.minus(n)
    case Neg{n}:
      Pos{1n+n}

def Int.add(a: Int, b: Int) -> Int:
  match a b:
    case Pos{x} Pos{y}:
      Pos{Nat.add(x, y)}
    case Pos{x} Neg{y}:
      Int.sub_nat(x, 1n+y)
    case Neg{x} Pos{y}:
      Int.sub_nat(y, 1n+x)
    case Neg{x} Neg{y}:
      Neg{1n+Nat.add(x, y)}

def Int.sub(a: Int, b: Int) -> Int:
  Int.add(a, Int.neg(b))

def Int.mul(a: Int, b: Int) -> Int:
  match a b:
    case Pos{x} Pos{y}:
      Pos{Nat.mul(x, y)}
    case Pos{x} Neg{y}:
      Int.minus(Nat.mul(x, 1n+y))
    case Neg{x} Pos{y}:
      Int.minus(Nat.mul(1n+x, y))
    case Neg{x} Neg{y}:
      Pos{Nat.mul(1n+x, 1n+y)}

def Int.abs(a: Int) -> Nat:
  match a:
    case Pos{n}:
      n
    case Neg{n}:
      1n+n

# Truncating division by a natural; used only where d divides |a|.
def Int.div_nat(a: Int, d: Nat) -> Int:
  match a:
    case Pos{n}:
      Pos{Nat.div(n, d)}
    case Neg{n}:
      Int.minus(Nat.div(1n+n, d))

def Int.cmp(a: Int, b: Int) -> Cmp:
  match a b:
    case Pos{x} Pos{y}:
      Nat.cmp(x, y)
    case Pos{x} Neg{y}:
      GT{}
    case Neg{x} Pos{y}:
      LT{}
    case Neg{x} Neg{y}:
      Nat.cmp(y, x)

def Int.is_eq(a: Int, b: Int) -> Bool:
  Cmp.is_eq(Int.cmp(a, b))

def Int.is_le(a: Int, b: Int) -> Bool:
  Cmp.is_le(Int.cmp(a, b))

def Int.show(a: Int) -> String:
  match a:
    case Pos{n}:
      Nat.show(n)
    case Neg{n}:
      "-" ++ Nat.show(1n+n)

# Rat
# ---

# num / (1 + dpred): the denominator is positive by construction.
# Every Rat this module builds is in lowest terms (gcd(|num|, den) = 1),
# so two such Rats are equal exactly when the numbers they denote are.
type Rat is Data:
  Rat{num: Int, dpred: Nat}

def Rat.num(r: Rat) -> Int:
  match r:
    case Rat{n, d}:
      n

def Rat.den(r: Rat) -> Nat:
  match r:
    case Rat{n, d}:
      1n+d

def Rat.zero() -> Rat:
  Rat{Pos{0n}, 0n}

def Rat.one() -> Rat:
  Rat{Pos{1n}, 0n}

def Rat.of_int(n: Int) -> Rat:
  Rat{n, 0n}

def Rat.reduce.go(n: Int, +d: Nat, +g: Nat) -> Rat:
  Rat{Int.div_nat(n, g), Nat.sub(Nat.div(d, g), 1n)}

# n / (1 + dp) in lowest terms; g >= 1 because 1 + dp > 0.
def Rat.reduce(+n: Int, +dp: Nat) -> Rat:
  Rat.reduce.go(n, 1n+dp, Nat.gcd(Int.abs(n), 1n+dp))

# n / d, or None when d is 0.
def Rat.make(n: Int, d: Int) -> Maybe<Rat>:
  match d:
    case Pos{0n}:
      None{}
    case Pos{1n+p}:
      Some{Rat.reduce(n, p)}
    case Neg{p}:
      Some{Rat.reduce(Int.neg(n), p)}

def Rat.neg(a: Rat) -> Rat:
  match a:
    case Rat{n, d}:
      Rat{Int.neg(n), d}

def Rat.add(a: Rat, b: Rat) -> Rat:
  match a b:
    case Rat{x, +p} Rat{y, +q}:
      Rat.reduce(Int.add(Int.mul(x, Pos{1n+q}), Int.mul(y, Pos{1n+p})), Nat.mul_pred(p, q))

def Rat.sub(a: Rat, b: Rat) -> Rat:
  Rat.add(a, Rat.neg(b))

def Rat.mul(a: Rat, b: Rat) -> Rat:
  match a b:
    case Rat{x, p} Rat{y, q}:
      Rat.reduce(Int.mul(x, y), Nat.mul_pred(p, q))

# 1 / a, or None when a is 0. Swapping a reduced fraction keeps it reduced.
def Rat.inv(a: Rat) -> Maybe<Rat>:
  match a:
    case Rat{Pos{0n}, d}:
      None{}
    case Rat{Pos{1n+n}, d}:
      Some{Rat{Pos{1n+d}, n}}
    case Rat{Neg{n}, d}:
      Some{Rat{Neg{d}, n}}

def Rat.div.go(a: Rat, ib: Maybe<Rat>) -> Maybe<Rat>:
  match ib:
    case None{}:
      None{}
    case Some{i}:
      Some{Rat.mul(a, i)}

# a / b, or None when b is 0.
def Rat.div(a: Rat, b: Rat) -> Maybe<Rat>:
  Rat.div.go(a, Rat.inv(b))

# Cross-multiplying keeps the order because denominators are positive.
def Rat.cmp(a: Rat, b: Rat) -> Cmp:
  match a b:
    case Rat{x, p} Rat{y, q}:
      Int.cmp(Int.mul(x, Pos{1n+q}), Int.mul(y, Pos{1n+p}))

def Rat.is_eq(a: Rat, b: Rat) -> Bool:
  Cmp.is_eq(Rat.cmp(a, b))

def Rat.is_le(a: Rat, b: Rat) -> Bool:
  Cmp.is_le(Rat.cmp(a, b))

def Rat.show.den(d: Nat) -> String:
  match d:
    case 0n:
      ""
    case 1n+p:
      "/" ++ Nat.show(2n+p)

def Rat.show(r: Rat) -> String:
  match r:
    case Rat{n, d}:
      Int.show(n) ++ Rat.show.den(d)
