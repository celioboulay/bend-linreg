import Base
import ./num.bend as N
import ./p_nat.bend as PN
import ./p_ring.bend as R

# Int: every operation agrees with Nat arithmetic on differences
# sub_nat(a, b) = a - b, and a normalizer for Int polynomial identities.

law Nat.sub_zero_r:
  for +a: Nat
  {Nat.sub(a, 0n) == a : Nat}

def Nat.sub_zero_r(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

law sub_nat_zero:
  for +a: Nat
  {N.Int.sub_nat(a, 0n) == N.Pos{a} : N.Int}

def sub_nat_zero(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

law sub_nat_neg:
  for +b: Nat
  {N.Int.sub_nat(0n, 1n+b) == N.Neg{b} : N.Int}

def sub_nat_neg(b):
  %Nat.sub_zero_r(b) : {N.Neg{Nat.sub(b, 0n)} == N.Neg{_} : N.Int}
  {==}

law sub_nat_succ.go:
  for c: Bool
  for +a: Nat
  for +b: Nat
  {N.Int.sub_nat.go(c, 1n+a, 1n+b) == N.Int.sub_nat.go(c, a, b) : N.Int}

def sub_nat_succ.go(c, a, b):
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

law sub_nat_succ:
  for +a: Nat
  for +b: Nat
  {N.Int.sub_nat(1n+a, 1n+b) == N.Int.sub_nat(a, b) : N.Int}

def sub_nat_succ(a, b):
  sub_nat_succ.go(Nat.is_lt(a, b), a, b)

# 0 - n is minus(n)
law sub_nat_minus:
  for +n: Nat
  {N.Int.sub_nat(0n, n) == N.Int.minus(n) : N.Int}

def sub_nat_minus(n):
  match n:
    case 0n:
      {==}
    case 1n+m:
      sub_nat_neg(m)

# (k + a) - (k + b) == a - b
law cancel_l:
  for +k: Nat
  for +a: Nat
  for +b: Nat
  {N.Int.sub_nat(Nat.add(k, a), Nat.add(k, b)) == N.Int.sub_nat(a, b) : N.Int}

def cancel_l(k, a, b):
  match k:
    case 0n:
      {==}
    case 1n+j:
      %cancel_l(j, a, b) : {N.Int.sub_nat(1n+Nat.add(j, a), 1n+Nat.add(j, b)) == _ : N.Int}
      sub_nat_succ(Nat.add(j, a), Nat.add(j, b))

law swap_sum:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  for h: {Nat.add(a, d) == Nat.add(c, b) : Nat}
  {Nat.add(b, c) == Nat.add(d, a) : Nat}

def swap_sum(a, b, c, d, h):
  %PN.add_comm(a, d) : {Nat.add(b, c) == _ : Nat}
  %Equal.sym(Nat, Nat.add(a, d), Nat.add(c, b), h) : {Nat.add(b, c) == _ : Nat}
  PN.add_comm(b, c)

# a - b == c - d whenever a + d == c + b
law sub_nat_eq:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  for h: {Nat.add(a, d) == Nat.add(c, b) : Nat}
  {N.Int.sub_nat(a, b) == N.Int.sub_nat(c, d) : N.Int}

def sub_nat_eq(a, b, c, d, h):
  %cancel_l(d, a, b) : {_ == N.Int.sub_nat(c, d) : N.Int}
  %cancel_l(b, c, d) : {N.Int.sub_nat(Nat.add(d, a), Nat.add(d, b)) == _ : N.Int}
  %swap_sum(a, b, c, d, h)
    : {N.Int.sub_nat(_, Nat.add(d, b)) == N.Int.sub_nat(Nat.add(b, c), Nat.add(b, d)) : N.Int}
  %PN.add_comm(b, d)
    : {N.Int.sub_nat(Nat.add(b, c), _) == N.Int.sub_nat(Nat.add(b, c), Nat.add(b, d)) : N.Int}
  {==}

# Every Int is a difference of naturals.
def Int.pp(x: N.Int) -> Nat:
  match x:
    case N.Pos{n}:
      n
    case N.Neg{n}:
      0n

def Int.nn(x: N.Int) -> Nat:
  match x:
    case N.Pos{n}:
      0n
    case N.Neg{n}:
      1n+n

law split:
  for +x: N.Int
  {x == N.Int.sub_nat(Int.pp(x), Int.nn(x)) : N.Int}

def split(x):
  match x:
    case N.Pos{n}:
      Equal.sym(N.Int, N.Int.sub_nat(n, 0n), N.Pos{n}, sub_nat_zero(n))
    case N.Neg{n}:
      Equal.sym(N.Int, N.Int.sub_nat(0n, 1n+n), N.Neg{n}, sub_nat_neg(n))

law neg_def:
  for +a: Nat
  for +b: Nat
  {N.Int.neg(N.Int.sub_nat(a, b)) == N.Int.sub_nat(b, a) : N.Int}

def neg_def(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 1n+p 0n:
      Equal.sym(N.Int, N.Int.sub_nat(0n, 1n+p), N.Neg{p}, sub_nat_neg(p))
    case 0n 1n+q:
      %Equal.sym(N.Int, N.Int.sub_nat(0n, 1n+q), N.Neg{q}, sub_nat_neg(q))
        : {N.Int.neg(_) == N.Int.sub_nat(1n+q, 0n) : N.Int}
      {==}
    case 1n+p 1n+q:
      %Equal.sym(N.Int, N.Int.sub_nat(1n+p, 1n+q), N.Int.sub_nat(p, q), sub_nat_succ(p, q))
        : {N.Int.neg(_) == N.Int.sub_nat(1n+q, 1n+p) : N.Int}
      %Equal.sym(N.Int, N.Int.sub_nat(1n+q, 1n+p), N.Int.sub_nat(q, p), sub_nat_succ(q, p))
        : {N.Int.neg(N.Int.sub_nat(p, q)) == _ : N.Int}
      neg_def(p, q)

law abs_def:
  for +a: Nat
  for +b: Nat
  {N.Int.abs(N.Int.sub_nat(a, b)) == Nat.add(Nat.sub(a, b), Nat.sub(b, a)) : Nat}

def abs_def(a, b):
  match a b:
    case 0n 0n:
      {==}
    case 1n+p 0n:
      Equal.sym(Nat, Nat.add(1n+p, 0n), 1n+p, PN.add_zero_r(1n+p))
    case 0n 1n+q:
      %Equal.sym(N.Int, N.Int.sub_nat(0n, 1n+q), N.Neg{q}, sub_nat_neg(q))
        : {N.Int.abs(_) == 1n+q : Nat}
      {==}
    case 1n+p 1n+q:
      %Equal.sym(N.Int, N.Int.sub_nat(1n+p, 1n+q), N.Int.sub_nat(p, q), sub_nat_succ(p, q))
        : {N.Int.abs(_) == Nat.add(Nat.sub(p, q), Nat.sub(q, p)) : Nat}
      abs_def(p, q)

# Addition
# --------

law addA:
  for +a: Nat
  for +c: Nat
  for +d: Nat
  {N.Int.add(N.Pos{a}, N.Int.sub_nat(c, d)) == N.Int.sub_nat(Nat.add(a, c), d) : N.Int}

def addA(a, c, d):
  match c d:
    case 0n 0n:
      Equal.sym(N.Int, N.Int.sub_nat(Nat.add(a, 0n), 0n), N.Pos{Nat.add(a, 0n)}, sub_nat_zero(Nat.add(a, 0n)))
    case 1n+p 0n:
      Equal.sym(N.Int, N.Int.sub_nat(Nat.add(a, 1n+p), 0n), N.Pos{Nat.add(a, 1n+p)}, sub_nat_zero(Nat.add(a, 1n+p)))
    case 0n 1n+q:
      %Equal.sym(N.Int, N.Int.sub_nat(0n, 1n+q), N.Neg{q}, sub_nat_neg(q))
        : {N.Int.add(N.Pos{a}, _) == N.Int.sub_nat(Nat.add(a, 0n), 1n+q) : N.Int}
      %PN.add_zero_r(a) : {N.Int.sub_nat(_, 1n+q) == N.Int.sub_nat(Nat.add(a, 0n), 1n+q) : N.Int}
      {==}
    case 1n+p 1n+q:
      %Equal.sym(N.Int, N.Int.sub_nat(1n+p, 1n+q), N.Int.sub_nat(p, q), sub_nat_succ(p, q))
        : {N.Int.add(N.Pos{a}, _) == N.Int.sub_nat(Nat.add(a, 1n+p), 1n+q) : N.Int}
      %Equal.sym(N.Int, N.Int.add(N.Pos{a}, N.Int.sub_nat(p, q)), N.Int.sub_nat(Nat.add(a, p), q), addA(a, p, q))
        : {_ == N.Int.sub_nat(Nat.add(a, 1n+p), 1n+q) : N.Int}
      %Equal.sym(Nat, Nat.add(a, 1n+p), 1n+Nat.add(a, p), PN.add_succ_r(a, p))
        : {N.Int.sub_nat(Nat.add(a, p), q) == N.Int.sub_nat(_, 1n+q) : N.Int}
      Equal.sym(N.Int, N.Int.sub_nat(1n+Nat.add(a, p), 1n+q), N.Int.sub_nat(Nat.add(a, p), q), sub_nat_succ(Nat.add(a, p), q))

law addB:
  for +a: Nat
  for +c: Nat
  for +d: Nat
  {N.Int.add(N.Neg{a}, N.Int.sub_nat(c, d)) == N.Int.sub_nat(c, 1n+Nat.add(a, d)) : N.Int}

def addB(a, c, d):
  match c d:
    case 0n 0n:
      %PN.add_zero_r(a) : {N.Int.sub_nat(0n, 1n+_) == N.Int.sub_nat(0n, 1n+Nat.add(a, 0n)) : N.Int}
      {==}
    case 1n+p 0n:
      %PN.add_zero_r(a) : {N.Int.sub_nat(1n+p, 1n+_) == N.Int.sub_nat(1n+p, 1n+Nat.add(a, 0n)) : N.Int}
      {==}
    case 0n 1n+q:
      %Equal.sym(N.Int, N.Int.sub_nat(0n, 1n+q), N.Neg{q}, sub_nat_neg(q))
        : {N.Int.add(N.Neg{a}, _) == N.Int.sub_nat(0n, 1n+Nat.add(a, 1n+q)) : N.Int}
      %Equal.sym(N.Int, N.Int.sub_nat(0n, 1n+Nat.add(a, 1n+q)), N.Neg{Nat.add(a, 1n+q)}, sub_nat_neg(Nat.add(a, 1n+q)))
        : {N.Neg{1n+Nat.add(a, q)} == _ : N.Int}
      %PN.add_succ_r(a, q) : {N.Neg{_} == N.Neg{Nat.add(a, 1n+q)} : N.Int}
      {==}
    case 1n+p 1n+q:
      %Equal.sym(N.Int, N.Int.sub_nat(1n+p, 1n+q), N.Int.sub_nat(p, q), sub_nat_succ(p, q))
        : {N.Int.add(N.Neg{a}, _) == N.Int.sub_nat(1n+p, 1n+Nat.add(a, 1n+q)) : N.Int}
      %Equal.sym(N.Int, N.Int.add(N.Neg{a}, N.Int.sub_nat(p, q)), N.Int.sub_nat(p, 1n+Nat.add(a, q)), addB(a, p, q))
        : {_ == N.Int.sub_nat(1n+p, 1n+Nat.add(a, 1n+q)) : N.Int}
      %Equal.sym(Nat, Nat.add(a, 1n+q), 1n+Nat.add(a, q), PN.add_succ_r(a, q))
        : {N.Int.sub_nat(p, 1n+Nat.add(a, q)) == N.Int.sub_nat(1n+p, 1n+_) : N.Int}
      Equal.sym(N.Int, N.Int.sub_nat(1n+p, 1n+1n+Nat.add(a, q)), N.Int.sub_nat(p, 1n+Nat.add(a, q)),
        sub_nat_succ(p, 1n+Nat.add(a, q)))

law add_def:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  {N.Int.add(N.Int.sub_nat(a, b), N.Int.sub_nat(c, d)) == N.Int.sub_nat(Nat.add(a, c), Nat.add(b, d)) : N.Int}

def add_def(a, b, c, d):
  match a b:
    case 0n 0n:
      addA(0n, c, d)
    case 1n+p 0n:
      addA(1n+p, c, d)
    case 0n 1n+q:
      %Equal.sym(N.Int, N.Int.sub_nat(0n, 1n+q), N.Neg{q}, sub_nat_neg(q))
        : {N.Int.add(_, N.Int.sub_nat(c, d)) == N.Int.sub_nat(c, 1n+Nat.add(q, d)) : N.Int}
      addB(q, c, d)
    case 1n+p 1n+q:
      %Equal.sym(N.Int, N.Int.sub_nat(1n+p, 1n+q), N.Int.sub_nat(p, q), sub_nat_succ(p, q))
        : {N.Int.add(_, N.Int.sub_nat(c, d)) == N.Int.sub_nat(1n+Nat.add(p, c), 1n+Nat.add(q, d)) : N.Int}
      %Equal.sym(N.Int, N.Int.add(N.Int.sub_nat(p, q), N.Int.sub_nat(c, d)), N.Int.sub_nat(Nat.add(p, c), Nat.add(q, d)),
          add_def(p, q, c, d))
        : {_ == N.Int.sub_nat(1n+Nat.add(p, c), 1n+Nat.add(q, d)) : N.Int}
      Equal.sym(N.Int, N.Int.sub_nat(1n+Nat.add(p, c), 1n+Nat.add(q, d)), N.Int.sub_nat(Nat.add(p, c), Nat.add(q, d)),
        sub_nat_succ(Nat.add(p, c), Nat.add(q, d)))

# Multiplication
# --------------

law mulC:
  for +a: Nat
  for +c: Nat
  for +d: Nat
  {N.Int.mul(N.Pos{a}, N.Int.sub_nat(c, d)) == N.Int.sub_nat(Nat.mul(a, c), Nat.mul(a, d)) : N.Int}

def mulC(a, c, d):
  match c d:
    case 0n 0n:
      %Equal.sym(Nat, Nat.mul(a, 0n), 0n, PN.mul_zero_r(a)) : {N.Pos{_} == N.Int.sub_nat(_, _) : N.Int}
      {==}
    case 1n+p 0n:
      %Equal.sym(Nat, Nat.mul(a, 0n), 0n, PN.mul_zero_r(a))
        : {N.Pos{Nat.mul(a, 1n+p)} == N.Int.sub_nat(Nat.mul(a, 1n+p), _) : N.Int}
      Equal.sym(N.Int, N.Int.sub_nat(Nat.mul(a, 1n+p), 0n), N.Pos{Nat.mul(a, 1n+p)}, sub_nat_zero(Nat.mul(a, 1n+p)))
    case 0n 1n+q:
      %Equal.sym(N.Int, N.Int.sub_nat(0n, 1n+q), N.Neg{q}, sub_nat_neg(q))
        : {N.Int.mul(N.Pos{a}, _) == N.Int.sub_nat(Nat.mul(a, 0n), Nat.mul(a, 1n+q)) : N.Int}
      %Equal.sym(Nat, Nat.mul(a, 0n), 0n, PN.mul_zero_r(a))
        : {N.Int.minus(Nat.mul(a, 1n+q)) == N.Int.sub_nat(_, Nat.mul(a, 1n+q)) : N.Int}
      Equal.sym(N.Int, N.Int.sub_nat(0n, Nat.mul(a, 1n+q)), N.Int.minus(Nat.mul(a, 1n+q)), sub_nat_minus(Nat.mul(a, 1n+q)))
    case 1n+p 1n+q:
      %Equal.sym(N.Int, N.Int.sub_nat(1n+p, 1n+q), N.Int.sub_nat(p, q), sub_nat_succ(p, q))
        : {N.Int.mul(N.Pos{a}, _) == N.Int.sub_nat(Nat.mul(a, 1n+p), Nat.mul(a, 1n+q)) : N.Int}
      %Equal.sym(N.Int, N.Int.mul(N.Pos{a}, N.Int.sub_nat(p, q)), N.Int.sub_nat(Nat.mul(a, p), Nat.mul(a, q)), mulC(a, p, q))
        : {_ == N.Int.sub_nat(Nat.mul(a, 1n+p), Nat.mul(a, 1n+q)) : N.Int}
      %Equal.sym(Nat, Nat.mul(a, 1n+p), Nat.add(a, Nat.mul(a, p)), PN.mul_succ_r(a, p))
        : {N.Int.sub_nat(Nat.mul(a, p), Nat.mul(a, q)) == N.Int.sub_nat(_, Nat.mul(a, 1n+q)) : N.Int}
      %Equal.sym(Nat, Nat.mul(a, 1n+q), Nat.add(a, Nat.mul(a, q)), PN.mul_succ_r(a, q))
        : {N.Int.sub_nat(Nat.mul(a, p), Nat.mul(a, q)) == N.Int.sub_nat(Nat.add(a, Nat.mul(a, p)), _) : N.Int}
      Equal.sym(N.Int, N.Int.sub_nat(Nat.add(a, Nat.mul(a, p)), Nat.add(a, Nat.mul(a, q))),
        N.Int.sub_nat(Nat.mul(a, p), Nat.mul(a, q)), cancel_l(a, Nat.mul(a, p), Nat.mul(a, q)))

law mulD:
  for +a: Nat
  for +c: Nat
  for +d: Nat
  {N.Int.mul(N.Neg{a}, N.Int.sub_nat(c, d)) == N.Int.sub_nat(Nat.mul(1n+a, d), Nat.mul(1n+a, c)) : N.Int}

def mulD(a, c, d):
  match c d:
    case 0n 0n:
      %Equal.sym(Nat, Nat.mul(1n+a, 0n), 0n, PN.mul_zero_r(1n+a)) : {N.Int.minus(_) == N.Int.sub_nat(_, _) : N.Int}
      {==}
    case 1n+p 0n:
      %Equal.sym(Nat, Nat.mul(1n+a, 0n), 0n, PN.mul_zero_r(1n+a))
        : {N.Int.minus(Nat.mul(1n+a, 1n+p)) == N.Int.sub_nat(_, Nat.mul(1n+a, 1n+p)) : N.Int}
      Equal.sym(N.Int, N.Int.sub_nat(0n, Nat.mul(1n+a, 1n+p)), N.Int.minus(Nat.mul(1n+a, 1n+p)),
        sub_nat_minus(Nat.mul(1n+a, 1n+p)))
    case 0n 1n+q:
      %Equal.sym(N.Int, N.Int.sub_nat(0n, 1n+q), N.Neg{q}, sub_nat_neg(q))
        : {N.Int.mul(N.Neg{a}, _) == N.Int.sub_nat(Nat.mul(1n+a, 1n+q), Nat.mul(1n+a, 0n)) : N.Int}
      %Equal.sym(Nat, Nat.mul(1n+a, 0n), 0n, PN.mul_zero_r(1n+a))
        : {N.Pos{Nat.mul(1n+a, 1n+q)} == N.Int.sub_nat(Nat.mul(1n+a, 1n+q), _) : N.Int}
      Equal.sym(N.Int, N.Int.sub_nat(Nat.mul(1n+a, 1n+q), 0n), N.Pos{Nat.mul(1n+a, 1n+q)}, sub_nat_zero(Nat.mul(1n+a, 1n+q)))
    case 1n+p 1n+q:
      %Equal.sym(N.Int, N.Int.sub_nat(1n+p, 1n+q), N.Int.sub_nat(p, q), sub_nat_succ(p, q))
        : {N.Int.mul(N.Neg{a}, _) == N.Int.sub_nat(Nat.mul(1n+a, 1n+q), Nat.mul(1n+a, 1n+p)) : N.Int}
      %Equal.sym(N.Int, N.Int.mul(N.Neg{a}, N.Int.sub_nat(p, q)), N.Int.sub_nat(Nat.mul(1n+a, q), Nat.mul(1n+a, p)), mulD(a, p, q))
        : {_ == N.Int.sub_nat(Nat.mul(1n+a, 1n+q), Nat.mul(1n+a, 1n+p)) : N.Int}
      %Equal.sym(Nat, Nat.mul(1n+a, 1n+q), Nat.add(1n+a, Nat.mul(1n+a, q)), PN.mul_succ_r(1n+a, q))
        : {N.Int.sub_nat(Nat.mul(1n+a, q), Nat.mul(1n+a, p)) == N.Int.sub_nat(_, Nat.mul(1n+a, 1n+p)) : N.Int}
      %Equal.sym(Nat, Nat.mul(1n+a, 1n+p), Nat.add(1n+a, Nat.mul(1n+a, p)), PN.mul_succ_r(1n+a, p))
        : {N.Int.sub_nat(Nat.mul(1n+a, q), Nat.mul(1n+a, p)) == N.Int.sub_nat(Nat.add(1n+a, Nat.mul(1n+a, q)), _) : N.Int}
      Equal.sym(N.Int, N.Int.sub_nat(Nat.add(1n+a, Nat.mul(1n+a, q)), Nat.add(1n+a, Nat.mul(1n+a, p))),
        N.Int.sub_nat(Nat.mul(1n+a, q), Nat.mul(1n+a, p)), cancel_l(1n+a, Nat.mul(1n+a, q), Nat.mul(1n+a, p)))

# (p c + q d) + ((1+p) d + (1+q) c) == ((1+p) c + (1+q) d) + (p d + q c)
law mul_step:
  for +p: Nat
  for +q: Nat
  for +c: Nat
  for +d: Nat
  {Nat.add(Nat.add(Nat.mul(p, c), Nat.mul(q, d)), Nat.add(Nat.mul(1n+p, d), Nat.mul(1n+q, c)))
    == Nat.add(Nat.add(Nat.mul(1n+p, c), Nat.mul(1n+q, d)), Nat.add(Nat.mul(p, d), Nat.mul(q, c))) : Nat}

def mul_step(p, q, c, d):
  R.Ring.eq(
    R.EAdd{R.EAdd{R.EMul{R.EVar{0n}, R.EVar{2n}}, R.EMul{R.EVar{1n}, R.EVar{3n}}},
           R.EAdd{R.EMul{R.EAdd{R.ENum{1n}, R.EVar{0n}}, R.EVar{3n}}, R.EMul{R.EAdd{R.ENum{1n}, R.EVar{1n}}, R.EVar{2n}}}},
    R.EAdd{R.EAdd{R.EMul{R.EAdd{R.ENum{1n}, R.EVar{0n}}, R.EVar{2n}}, R.EMul{R.EAdd{R.ENum{1n}, R.EVar{1n}}, R.EVar{3n}}},
           R.EAdd{R.EMul{R.EVar{0n}, R.EVar{3n}}, R.EMul{R.EVar{1n}, R.EVar{2n}}}},
    [p, q, c, d], {==})

law mul_def:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  {N.Int.mul(N.Int.sub_nat(a, b), N.Int.sub_nat(c, d))
    == N.Int.sub_nat(Nat.add(Nat.mul(a, c), Nat.mul(b, d)), Nat.add(Nat.mul(a, d), Nat.mul(b, c))) : N.Int}

def mul_def(a, b, c, d):
  match a b:
    case 0n 0n:
      mulC(0n, c, d)
    case 1n+p 0n:
      %Equal.sym(Nat, Nat.add(Nat.mul(1n+p, c), 0n), Nat.mul(1n+p, c), PN.add_zero_r(Nat.mul(1n+p, c)))
        : {N.Int.mul(N.Pos{1n+p}, N.Int.sub_nat(c, d)) == N.Int.sub_nat(_, Nat.add(Nat.mul(1n+p, d), 0n)) : N.Int}
      %Equal.sym(Nat, Nat.add(Nat.mul(1n+p, d), 0n), Nat.mul(1n+p, d), PN.add_zero_r(Nat.mul(1n+p, d)))
        : {N.Int.mul(N.Pos{1n+p}, N.Int.sub_nat(c, d)) == N.Int.sub_nat(Nat.mul(1n+p, c), _) : N.Int}
      mulC(1n+p, c, d)
    case 0n 1n+q:
      %Equal.sym(N.Int, N.Int.sub_nat(0n, 1n+q), N.Neg{q}, sub_nat_neg(q))
        : {N.Int.mul(_, N.Int.sub_nat(c, d)) == N.Int.sub_nat(Nat.mul(1n+q, d), Nat.mul(1n+q, c)) : N.Int}
      mulD(q, c, d)
    case 1n+p 1n+q:
      %Equal.sym(N.Int, N.Int.sub_nat(1n+p, 1n+q), N.Int.sub_nat(p, q), sub_nat_succ(p, q))
        : {N.Int.mul(_, N.Int.sub_nat(c, d))
            == N.Int.sub_nat(Nat.add(Nat.mul(1n+p, c), Nat.mul(1n+q, d)), Nat.add(Nat.mul(1n+p, d), Nat.mul(1n+q, c))) : N.Int}
      %Equal.sym(N.Int, N.Int.mul(N.Int.sub_nat(p, q), N.Int.sub_nat(c, d)),
          N.Int.sub_nat(Nat.add(Nat.mul(p, c), Nat.mul(q, d)), Nat.add(Nat.mul(p, d), Nat.mul(q, c))), mul_def(p, q, c, d))
        : {_ == N.Int.sub_nat(Nat.add(Nat.mul(1n+p, c), Nat.mul(1n+q, d)), Nat.add(Nat.mul(1n+p, d), Nat.mul(1n+q, c))) : N.Int}
      sub_nat_eq(Nat.add(Nat.mul(p, c), Nat.mul(q, d)), Nat.add(Nat.mul(p, d), Nat.mul(q, c)),
        Nat.add(Nat.mul(1n+p, c), Nat.mul(1n+q, d)), Nat.add(Nat.mul(1n+p, d), Nat.mul(1n+q, c)),
        mul_step(p, q, c, d))

# Comparison
# ----------

law cmpP:
  for +a: Nat
  for +c: Nat
  for +d: Nat
  {N.Int.cmp(N.Pos{a}, N.Int.sub_nat(c, d)) == Nat.cmp(Nat.add(a, d), Nat.add(c, 0n)) : Cmp}

def cmpP(a, c, d):
  match c d:
    case 0n 0n:
      %PN.add_zero_r(a) : {Nat.cmp(_, 0n) == Nat.cmp(Nat.add(a, 0n), 0n) : Cmp}
      {==}
    case 1n+r 0n:
      %PN.add_zero_r(a) : {Nat.cmp(_, 1n+r) == Nat.cmp(Nat.add(a, 0n), 1n+Nat.add(r, 0n)) : Cmp}
      %PN.add_zero_r(r) : {Nat.cmp(Nat.add(a, 0n), 1n+_) == Nat.cmp(Nat.add(a, 0n), 1n+Nat.add(r, 0n)) : Cmp}
      {==}
    case 0n 1n+s:
      %Equal.sym(N.Int, N.Int.sub_nat(0n, 1n+s), N.Neg{s}, sub_nat_neg(s))
        : {N.Int.cmp(N.Pos{a}, _) == Nat.cmp(Nat.add(a, 1n+s), 0n) : Cmp}
      %Equal.sym(Nat, Nat.add(a, 1n+s), 1n+Nat.add(a, s), PN.add_succ_r(a, s)) : {GT{} == Nat.cmp(_, 0n) : Cmp}
      {==}
    case 1n+r 1n+s:
      %Equal.sym(N.Int, N.Int.sub_nat(1n+r, 1n+s), N.Int.sub_nat(r, s), sub_nat_succ(r, s))
        : {N.Int.cmp(N.Pos{a}, _) == Nat.cmp(Nat.add(a, 1n+s), 1n+Nat.add(r, 0n)) : Cmp}
      %Equal.sym(Cmp, N.Int.cmp(N.Pos{a}, N.Int.sub_nat(r, s)), Nat.cmp(Nat.add(a, s), Nat.add(r, 0n)), cmpP(a, r, s))
        : {_ == Nat.cmp(Nat.add(a, 1n+s), 1n+Nat.add(r, 0n)) : Cmp}
      %Equal.sym(Nat, Nat.add(a, 1n+s), 1n+Nat.add(a, s), PN.add_succ_r(a, s))
        : {Nat.cmp(Nat.add(a, s), Nat.add(r, 0n)) == Nat.cmp(_, 1n+Nat.add(r, 0n)) : Cmp}
      {==}

law cmpN:
  for +q: Nat
  for +c: Nat
  for +d: Nat
  {N.Int.cmp(N.Neg{q}, N.Int.sub_nat(c, d)) == Nat.cmp(d, Nat.add(c, 1n+q)) : Cmp}

def cmpN(q, c, d):
  match c d:
    case 0n 0n:
      {==}
    case 1n+r 0n:
      {==}
    case 0n 1n+s:
      %Equal.sym(N.Int, N.Int.sub_nat(0n, 1n+s), N.Neg{s}, sub_nat_neg(s))
        : {N.Int.cmp(N.Neg{q}, _) == Nat.cmp(1n+s, 1n+q) : Cmp}
      {==}
    case 1n+r 1n+s:
      %Equal.sym(N.Int, N.Int.sub_nat(1n+r, 1n+s), N.Int.sub_nat(r, s), sub_nat_succ(r, s))
        : {N.Int.cmp(N.Neg{q}, _) == Nat.cmp(1n+s, Nat.add(1n+r, 1n+q)) : Cmp}
      cmpN(q, r, s)

law cmp_def:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  {N.Int.cmp(N.Int.sub_nat(a, b), N.Int.sub_nat(c, d)) == Nat.cmp(Nat.add(a, d), Nat.add(c, b)) : Cmp}

def cmp_def(a, b, c, d):
  match a b:
    case 0n 0n:
      cmpP(0n, c, d)
    case 1n+p 0n:
      cmpP(1n+p, c, d)
    case 0n 1n+q:
      %Equal.sym(N.Int, N.Int.sub_nat(0n, 1n+q), N.Neg{q}, sub_nat_neg(q))
        : {N.Int.cmp(_, N.Int.sub_nat(c, d)) == Nat.cmp(d, Nat.add(c, 1n+q)) : Cmp}
      cmpN(q, c, d)
    case 1n+p 1n+q:
      %Equal.sym(N.Int, N.Int.sub_nat(1n+p, 1n+q), N.Int.sub_nat(p, q), sub_nat_succ(p, q))
        : {N.Int.cmp(_, N.Int.sub_nat(c, d)) == Nat.cmp(1n+Nat.add(p, d), Nat.add(c, 1n+q)) : Cmp}
      %Equal.sym(Cmp, N.Int.cmp(N.Int.sub_nat(p, q), N.Int.sub_nat(c, d)), Nat.cmp(Nat.add(p, d), Nat.add(c, q)), cmp_def(p, q, c, d))
        : {_ == Nat.cmp(1n+Nat.add(p, d), Nat.add(c, 1n+q)) : Cmp}
      %Equal.sym(Nat, Nat.add(c, 1n+q), 1n+Nat.add(c, q), PN.add_succ_r(c, q))
        : {Nat.cmp(Nat.add(p, d), Nat.add(c, q)) == Nat.cmp(1n+Nat.add(p, d), _) : Cmp}
      {==}

law eq_def:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  {N.Int.is_eq(N.Int.sub_nat(a, b), N.Int.sub_nat(c, d)) == Nat.is_eq(Nat.add(a, d), Nat.add(c, b)) : Bool}

def eq_def(a, b, c, d):
  %cmp_def(a, b, c, d) : {Cmp.is_eq(N.Int.cmp(N.Int.sub_nat(a, b), N.Int.sub_nat(c, d))) == Cmp.is_eq(_) : Bool}
  {==}

law le_def:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  {N.Int.is_le(N.Int.sub_nat(a, b), N.Int.sub_nat(c, d)) == Nat.is_le(Nat.add(a, d), Nat.add(c, b)) : Bool}

def le_def(a, b, c, d):
  %cmp_def(a, b, c, d) : {Cmp.is_le(N.Int.cmp(N.Int.sub_nat(a, b), N.Int.sub_nat(c, d))) == Cmp.is_le(_) : Bool}
  {==}

# Int normalizer
# --------------
# An Int expression is evaluated as P - N for two Nat expressions (its
# positive and negative parts, tr(e, True) and tr(e, False)), so an Int
# identity e1 == e2 follows from the Nat identity P1 + N2 == P2 + N1:
#   IRing.eq(e1, e2, env, {==}) : {IEx.eval(e1, env) == IEx.eval(e2, env) : N.Int}

type IEx is Data:
  IVar{i: Nat}
  IConst{z: N.Int}
  IAdd{a: IEx, b: IEx}
  IMul{a: IEx, b: IEx}
  INeg{a: IEx}

def IEnv.get(env: +List<N.Int>, +i: Nat) -> N.Int:
  match env:
    case Nil{}:
      N.Pos{0n}
    case Con{h, t}:
      match i:
        case 0n:
          h
        case 1n+j:
          IEnv.get(t, j)

def IEx.eval(e: IEx, +env: +List<N.Int>) -> N.Int:
  match e:
    case IVar{i}:
      IEnv.get(env, i)
    case IConst{z}:
      z
    case IAdd{a, b}:
      N.Int.add(IEx.eval(a, env), IEx.eval(b, env))
    case IMul{a, b}:
      N.Int.mul(IEx.eval(a, env), IEx.eval(b, env))
    case INeg{a}:
      N.Int.neg(IEx.eval(a, env))

# [pp x0, nn x0, pp x1, nn x1, ...]
def IEnv.nat(env: +List<N.Int>) -> +List<Nat>:
  match env:
    case Nil{}:
      Nil{}
    case Con{+x, t}:
      Int.pp(x) <> Int.nn(x) <> IEnv.nat(t)

# The positive (side True) or negative (side False) part of e.
def IEx.tr(e: IEx, +side: Bool) -> R.Ex:
  match e:
    case IVar{i}:
      match side:
        case True{}:
          R.EVar{Nat.double(i)}
        case False{}:
          R.EVar{1n+Nat.double(i)}
    case IConst{z}:
      match side:
        case True{}:
          R.ENum{Int.pp(z)}
        case False{}:
          R.ENum{Int.nn(z)}
    case IAdd{a, b}:
      R.EAdd{IEx.tr(a, side), IEx.tr(b, side)}
    case IMul{+a, +b}:
      match side:
        case True{}:
          R.EAdd{R.EMul{IEx.tr(a, True{}), IEx.tr(b, True{})}, R.EMul{IEx.tr(a, False{}), IEx.tr(b, False{})}}
        case False{}:
          R.EAdd{R.EMul{IEx.tr(a, True{}), IEx.tr(b, False{})}, R.EMul{IEx.tr(a, False{}), IEx.tr(b, True{})}}
    case INeg{a}:
      IEx.tr(a, Bool.not(side))

law IEnv.get_ok:
  for +env: +List<N.Int>
  for +i: Nat
  {IEnv.get(env, i)
    == N.Int.sub_nat(R.Env.get(IEnv.nat(env), Nat.double(i)), R.Env.get(IEnv.nat(env), 1n+Nat.double(i))) : N.Int}

def IEnv.get_ok(env, i):
  match env:
    case Nil{}:
      {==}
    case Con{x, t}:
      match i:
        case 0n:
          split(x)
        case 1n+j:
          IEnv.get_ok(t, j)

law IEx.tr_ok:
  for +e: IEx
  for +env: +List<N.Int>
  {IEx.eval(e, env)
    == N.Int.sub_nat(R.Ex.eval(IEx.tr(e, True{}), IEnv.nat(env)), R.Ex.eval(IEx.tr(e, False{}), IEnv.nat(env))) : N.Int}

def IEx.tr_ok(e, env):
  match e:
    case IVar{i}:
      IEnv.get_ok(env, i)
    case IConst{z}:
      split(z)
    case IAdd{a, b}:
      %Equal.sym(N.Int, IEx.eval(a, env),
          N.Int.sub_nat(R.Ex.eval(IEx.tr(a, True{}), IEnv.nat(env)), R.Ex.eval(IEx.tr(a, False{}), IEnv.nat(env))),
          IEx.tr_ok(a, env))
        : {N.Int.add(_, IEx.eval(b, env))
            == N.Int.sub_nat(Nat.add(R.Ex.eval(IEx.tr(a, True{}), IEnv.nat(env)), R.Ex.eval(IEx.tr(b, True{}), IEnv.nat(env))),
                             Nat.add(R.Ex.eval(IEx.tr(a, False{}), IEnv.nat(env)), R.Ex.eval(IEx.tr(b, False{}), IEnv.nat(env)))) : N.Int}
      %Equal.sym(N.Int, IEx.eval(b, env),
          N.Int.sub_nat(R.Ex.eval(IEx.tr(b, True{}), IEnv.nat(env)), R.Ex.eval(IEx.tr(b, False{}), IEnv.nat(env))),
          IEx.tr_ok(b, env))
        : {N.Int.add(N.Int.sub_nat(R.Ex.eval(IEx.tr(a, True{}), IEnv.nat(env)), R.Ex.eval(IEx.tr(a, False{}), IEnv.nat(env))), _)
            == N.Int.sub_nat(Nat.add(R.Ex.eval(IEx.tr(a, True{}), IEnv.nat(env)), R.Ex.eval(IEx.tr(b, True{}), IEnv.nat(env))),
                             Nat.add(R.Ex.eval(IEx.tr(a, False{}), IEnv.nat(env)), R.Ex.eval(IEx.tr(b, False{}), IEnv.nat(env)))) : N.Int}
      add_def(R.Ex.eval(IEx.tr(a, True{}), IEnv.nat(env)), R.Ex.eval(IEx.tr(a, False{}), IEnv.nat(env)),
              R.Ex.eval(IEx.tr(b, True{}), IEnv.nat(env)), R.Ex.eval(IEx.tr(b, False{}), IEnv.nat(env)))
    case IMul{a, b}:
      %Equal.sym(N.Int, IEx.eval(a, env),
          N.Int.sub_nat(R.Ex.eval(IEx.tr(a, True{}), IEnv.nat(env)), R.Ex.eval(IEx.tr(a, False{}), IEnv.nat(env))),
          IEx.tr_ok(a, env))
        : {N.Int.mul(_, IEx.eval(b, env))
            == N.Int.sub_nat(
                 Nat.add(Nat.mul(R.Ex.eval(IEx.tr(a, True{}), IEnv.nat(env)), R.Ex.eval(IEx.tr(b, True{}), IEnv.nat(env))),
                         Nat.mul(R.Ex.eval(IEx.tr(a, False{}), IEnv.nat(env)), R.Ex.eval(IEx.tr(b, False{}), IEnv.nat(env)))),
                 Nat.add(Nat.mul(R.Ex.eval(IEx.tr(a, True{}), IEnv.nat(env)), R.Ex.eval(IEx.tr(b, False{}), IEnv.nat(env))),
                         Nat.mul(R.Ex.eval(IEx.tr(a, False{}), IEnv.nat(env)), R.Ex.eval(IEx.tr(b, True{}), IEnv.nat(env))))) : N.Int}
      %Equal.sym(N.Int, IEx.eval(b, env),
          N.Int.sub_nat(R.Ex.eval(IEx.tr(b, True{}), IEnv.nat(env)), R.Ex.eval(IEx.tr(b, False{}), IEnv.nat(env))),
          IEx.tr_ok(b, env))
        : {N.Int.mul(N.Int.sub_nat(R.Ex.eval(IEx.tr(a, True{}), IEnv.nat(env)), R.Ex.eval(IEx.tr(a, False{}), IEnv.nat(env))), _)
            == N.Int.sub_nat(
                 Nat.add(Nat.mul(R.Ex.eval(IEx.tr(a, True{}), IEnv.nat(env)), R.Ex.eval(IEx.tr(b, True{}), IEnv.nat(env))),
                         Nat.mul(R.Ex.eval(IEx.tr(a, False{}), IEnv.nat(env)), R.Ex.eval(IEx.tr(b, False{}), IEnv.nat(env)))),
                 Nat.add(Nat.mul(R.Ex.eval(IEx.tr(a, True{}), IEnv.nat(env)), R.Ex.eval(IEx.tr(b, False{}), IEnv.nat(env))),
                         Nat.mul(R.Ex.eval(IEx.tr(a, False{}), IEnv.nat(env)), R.Ex.eval(IEx.tr(b, True{}), IEnv.nat(env))))) : N.Int}
      mul_def(R.Ex.eval(IEx.tr(a, True{}), IEnv.nat(env)), R.Ex.eval(IEx.tr(a, False{}), IEnv.nat(env)),
              R.Ex.eval(IEx.tr(b, True{}), IEnv.nat(env)), R.Ex.eval(IEx.tr(b, False{}), IEnv.nat(env)))
    case INeg{a}:
      %Equal.sym(N.Int, IEx.eval(a, env),
          N.Int.sub_nat(R.Ex.eval(IEx.tr(a, True{}), IEnv.nat(env)), R.Ex.eval(IEx.tr(a, False{}), IEnv.nat(env))),
          IEx.tr_ok(a, env))
        : {N.Int.neg(_)
            == N.Int.sub_nat(R.Ex.eval(IEx.tr(a, False{}), IEnv.nat(env)), R.Ex.eval(IEx.tr(a, True{}), IEnv.nat(env))) : N.Int}
      neg_def(R.Ex.eval(IEx.tr(a, True{}), IEnv.nat(env)), R.Ex.eval(IEx.tr(a, False{}), IEnv.nat(env)))

# Two Int expressions whose parts satisfy P1 + N2 == P2 + N1 as Nat
# polynomials are equal.
law IRing.eq:
  for +e1: IEx
  for +e2: IEx
  for +env: +List<N.Int>
  for h: {R.Ex.norm(R.EAdd{IEx.tr(e1, True{}), IEx.tr(e2, False{})})
          == R.Ex.norm(R.EAdd{IEx.tr(e2, True{}), IEx.tr(e1, False{})}) : +List<R.Mono>}
  {IEx.eval(e1, env) == IEx.eval(e2, env) : N.Int}

def IRing.eq(e1, e2, env, h):
  %Equal.sym(N.Int, IEx.eval(e2, env),
      N.Int.sub_nat(R.Ex.eval(IEx.tr(e2, True{}), IEnv.nat(env)), R.Ex.eval(IEx.tr(e2, False{}), IEnv.nat(env))),
      IEx.tr_ok(e2, env))
    : {IEx.eval(e1, env) == _ : N.Int}
  %Equal.sym(N.Int, IEx.eval(e1, env),
      N.Int.sub_nat(R.Ex.eval(IEx.tr(e1, True{}), IEnv.nat(env)), R.Ex.eval(IEx.tr(e1, False{}), IEnv.nat(env))),
      IEx.tr_ok(e1, env))
    : {_ == N.Int.sub_nat(R.Ex.eval(IEx.tr(e2, True{}), IEnv.nat(env)), R.Ex.eval(IEx.tr(e2, False{}), IEnv.nat(env))) : N.Int}
  sub_nat_eq(
    R.Ex.eval(IEx.tr(e1, True{}), IEnv.nat(env)), R.Ex.eval(IEx.tr(e1, False{}), IEnv.nat(env)),
    R.Ex.eval(IEx.tr(e2, True{}), IEnv.nat(env)), R.Ex.eval(IEx.tr(e2, False{}), IEnv.nat(env)),
    R.Ring.eq(R.EAdd{IEx.tr(e1, True{}), IEx.tr(e2, False{})}, R.EAdd{IEx.tr(e2, True{}), IEx.tr(e1, False{})},
      IEnv.nat(env), h))

# Ring laws
# ---------

law Int.add_comm:
  for +a: N.Int
  for +b: N.Int
  {N.Int.add(a, b) == N.Int.add(b, a) : N.Int}

def Int.add_comm(a, b):
  IRing.eq(IAdd{IVar{0n}, IVar{1n}}, IAdd{IVar{1n}, IVar{0n}}, [a, b], {==})

law Int.add_assoc:
  for +a: N.Int
  for +b: N.Int
  for +c: N.Int
  {N.Int.add(N.Int.add(a, b), c) == N.Int.add(a, N.Int.add(b, c)) : N.Int}

def Int.add_assoc(a, b, c):
  IRing.eq(IAdd{IAdd{IVar{0n}, IVar{1n}}, IVar{2n}}, IAdd{IVar{0n}, IAdd{IVar{1n}, IVar{2n}}}, [a, b, c], {==})

law Int.mul_comm:
  for +a: N.Int
  for +b: N.Int
  {N.Int.mul(a, b) == N.Int.mul(b, a) : N.Int}

def Int.mul_comm(a, b):
  IRing.eq(IMul{IVar{0n}, IVar{1n}}, IMul{IVar{1n}, IVar{0n}}, [a, b], {==})

law Int.mul_assoc:
  for +a: N.Int
  for +b: N.Int
  for +c: N.Int
  {N.Int.mul(N.Int.mul(a, b), c) == N.Int.mul(a, N.Int.mul(b, c)) : N.Int}

def Int.mul_assoc(a, b, c):
  IRing.eq(IMul{IMul{IVar{0n}, IVar{1n}}, IVar{2n}}, IMul{IVar{0n}, IMul{IVar{1n}, IVar{2n}}}, [a, b, c], {==})

law Int.mul_add:
  for +a: N.Int
  for +b: N.Int
  for +c: N.Int
  {N.Int.mul(a, N.Int.add(b, c)) == N.Int.add(N.Int.mul(a, b), N.Int.mul(a, c)) : N.Int}

def Int.mul_add(a, b, c):
  IRing.eq(IMul{IVar{0n}, IAdd{IVar{1n}, IVar{2n}}}, IAdd{IMul{IVar{0n}, IVar{1n}}, IMul{IVar{0n}, IVar{2n}}}, [a, b, c], {==})
