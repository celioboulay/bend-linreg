import Base
import ./num.bend as N
import ./p_nat.bend as PN
import ./p_ring.bend as R
import ./p_int.bend as PI
import ./p_div.bend as PD
import ./p_rat.bend as PR
import ./p_sum.bend as PS
import ./p_size.bend as PZ
import ./p_reg.bend as PG
import ./LAWS.bend as Laws
import ./linreg.bend as L

# The fitted line: its residuals satisfy the normal equations, and no other
# line has a smaller (or equal) sum of squared residuals.

# Int order
# ---------

law sub_nat_add:
  for +m: Nat
  for +n: Nat
  {N.Int.sub_nat(Nat.add(m, n), m) == N.Pos{n} : N.Int}

def sub_nat_add(m, n):
  match m:
    case 0n:
      PI.sub_nat_zero(n)
    case 1n+p:
      Equal.trans(N.Int, N.Int.sub_nat(1n+Nat.add(p, n), 1n+p), N.Int.sub_nat(Nat.add(p, n), p), N.Pos{n},
        PI.sub_nat_succ(Nat.add(p, n), p), sub_nat_add(p, n))

law neg_gap:
  for +c: Nat
  for +n: Nat
  {N.Int.sub_nat(c, 1n+Nat.add(c, n)) == N.Neg{n} : N.Int}

def neg_gap(c, n):
  match c:
    case 0n:
      PI.sub_nat_neg(n)
    case 1n+p:
      Equal.trans(N.Int, N.Int.sub_nat(1n+p, 2n+Nat.add(p, n)), N.Int.sub_nat(p, 1n+Nat.add(p, n)), N.Neg{n},
        PI.sub_nat_succ(p, 1n+Nat.add(p, n)), neg_gap(p, n))

law add_of_le.pp:
  for +m: Nat
  for +n: Nat
  for w: PD.LeW(m, n)
  exs c: Nat
  {N.Pos{n} == N.Int.add(N.Pos{m}, N.Pos{c}) : N.Int}

def add_of_le.pp(m, n, w):
  match w:
    case (+c, e):
      (c, PG.pos_eq(n, Nat.add(m, c), e))

law add_of_le.nn:
  for +m: Nat
  for +n: Nat
  for w: PD.LeW(n, m)
  exs c: Nat
  {N.Neg{n} == N.Int.add(N.Neg{m}, N.Pos{c}) : N.Int}

def add_of_le.nn(m, n, w):
  match w:
    case (+c, e):
      (c, (%Equal.sym(Nat, m, Nat.add(n, c), e) : {N.Neg{n} == N.Int.sub_nat(c, 1n+_) : N.Int}
           %PN.add_comm(c, n) : {N.Neg{n} == N.Int.sub_nat(c, 1n+_) : N.Int}
           Equal.sym(N.Int, N.Int.sub_nat(c, 1n+Nat.add(c, n)), N.Neg{n}, neg_gap(c, n))))

# a <= b gives b == a + c for some c >= 0
law add_of_le:
  for +a: N.Int
  for +b: N.Int
  for h: {N.Int.is_le(a, b) == True{} : Bool}
  exs c: Nat
  {b == N.Int.add(a, N.Pos{c}) : N.Int}

def add_of_le(a, b, h):
  match a b:
    case N.Pos{m} N.Pos{n}:
      add_of_le.pp(m, n, PD.le_witness(m, n, h))
    case N.Pos{m} N.Neg{n}:
      Empty.absurd(&c: Nat -> {N.Neg{n} == N.Int.add(N.Pos{m}, N.Pos{c}) : N.Int}, PD.Bool.ft(h))
    case N.Neg{m} N.Pos{n}:
      (1n+Nat.add(m, n),
        Equal.sym(N.Int, N.Int.sub_nat(1n+Nat.add(m, n), 1n+m), N.Pos{n},
          Equal.trans(N.Int, N.Int.sub_nat(1n+Nat.add(m, n), 1n+m), N.Int.sub_nat(Nat.add(m, n), m), N.Pos{n},
            PI.sub_nat_succ(Nat.add(m, n), m), sub_nat_add(m, n))))
    case N.Neg{m} N.Neg{n}:
      add_of_le.nn(m, n, PD.le_witness(n, m, h))

law le_of_add.t:
  for +m: Nat
  for +c: Nat
  for w: PD.LeW(c, m)
  {N.Int.is_le(N.Neg{m}, N.Int.add(N.Neg{m}, N.Pos{c})) == True{} : Bool}

def le_of_add.t(m, c, w):
  match w:
    case (+d, e):
      %Equal.sym(Nat, m, Nat.add(c, d), e) : {N.Int.is_le(N.Neg{_}, N.Int.sub_nat(c, 1n+_)) == True{} : Bool}
      %Equal.sym(N.Int, N.Int.sub_nat(c, 1n+Nat.add(c, d)), N.Neg{d}, neg_gap(c, d))
        : {N.Int.is_le(N.Neg{Nat.add(c, d)}, _) == True{} : Bool}
      %PN.add_comm(d, c) : {Nat.is_le(d, _) == True{} : Bool}
      PD.le_plus(d, c)

law le_of_add.f:
  for +m: Nat
  for +c: Nat
  for w: PD.LeW(1n+m, c)
  {N.Int.is_le(N.Neg{m}, N.Int.add(N.Neg{m}, N.Pos{c})) == True{} : Bool}

def le_of_add.f(m, c, w):
  match w:
    case (+d, e):
      %Equal.sym(Nat, c, Nat.add(1n+m, d), e) : {N.Int.is_le(N.Neg{m}, N.Int.sub_nat(_, 1n+m)) == True{} : Bool}
      %Equal.sym(N.Int, N.Int.sub_nat(1n+Nat.add(m, d), 1n+m), N.Pos{d},
          Equal.trans(N.Int, N.Int.sub_nat(1n+Nat.add(m, d), 1n+m), N.Int.sub_nat(Nat.add(m, d), m), N.Pos{d},
            PI.sub_nat_succ(Nat.add(m, d), m), sub_nat_add(m, d)))
        : {N.Int.is_le(N.Neg{m}, _) == True{} : Bool}
      {==}

law le_of_add.go:
  for +m: Nat
  for +c: Nat
  for b: Bool
  for +e: {Nat.is_le(c, m) == b : Bool}
  {N.Int.is_le(N.Neg{m}, N.Int.add(N.Neg{m}, N.Pos{c})) == True{} : Bool}

def le_of_add.go(m, c, b, e):
  match b:
    case True{}:
      le_of_add.t(m, c, PD.le_witness(c, m, e))
    case False{}:
      le_of_add.f(m, c, PZ.le_false_w(c, m, e))

law le_of_add:
  for +a: N.Int
  for +c: Nat
  {N.Int.is_le(a, N.Int.add(a, N.Pos{c})) == True{} : Bool}

def le_of_add(a, c):
  match a:
    case N.Pos{m}:
      PD.le_plus(m, c)
    case N.Neg{m}:
      le_of_add.go(m, c, Nat.is_le(c, m), {==})

law isp_pos:
  for +z: N.Int
  for h: PR.Int.isp(z)
  exs n: Nat
  {z == N.Pos{n} : N.Int}

def isp_pos(z, h):
  match z:
    case N.Pos{n}:
      (n, {==})
    case N.Neg{n}:
      match h:

# a <= b keeps under a positive factor...
law le_mul_pos.go:
  for +a: N.Int
  for +b: N.Int
  for +k: Nat
  for +c: Nat
  for +e: {b == N.Int.add(a, N.Pos{c}) : N.Int}
  {N.Int.is_le(N.Int.mul(a, N.Pos{1n+k}), N.Int.mul(b, N.Pos{1n+k})) == True{} : Bool}

def le_mul_pos.go(a, b, k, c, e):
  %Equal.sym(N.Int, b, N.Int.add(a, N.Pos{c}), e)
    : {N.Int.is_le(N.Int.mul(a, N.Pos{1n+k}), N.Int.mul(_, N.Pos{1n+k})) == True{} : Bool}
  %Equal.sym(N.Int, N.Int.mul(N.Int.add(a, N.Pos{c}), N.Pos{1n+k}), N.Int.add(N.Int.mul(a, N.Pos{1n+k}), N.Pos{Nat.mul(c, 1n+k)}),
      PI.IRing.eq(PI.IMul{PI.IAdd{PI.IVar{0n}, PI.IVar{1n}}, PI.IVar{2n}}, PI.IAdd{PI.IMul{PI.IVar{0n}, PI.IVar{2n}}, PI.IMul{PI.IVar{1n}, PI.IVar{2n}}}, [a, N.Pos{c}, N.Pos{1n+k}], {==}))
    : {N.Int.is_le(N.Int.mul(a, N.Pos{1n+k}), _) == True{} : Bool}
  le_of_add(N.Int.mul(a, N.Pos{1n+k}), Nat.mul(c, 1n+k))

law le_mul_pos.w:
  for +a: N.Int
  for +b: N.Int
  for +k: Nat
  for w: &c: Nat -> {b == N.Int.add(a, N.Pos{c}) : N.Int}
  {N.Int.is_le(N.Int.mul(a, N.Pos{1n+k}), N.Int.mul(b, N.Pos{1n+k})) == True{} : Bool}

def le_mul_pos.w(a, b, k, w):
  match w:
    case (+c, e):
      le_mul_pos.go(a, b, k, c, e)

law le_mul_pos:
  for +a: N.Int
  for +b: N.Int
  for +k: Nat
  for h: {N.Int.is_le(a, b) == True{} : Bool}
  {N.Int.is_le(N.Int.mul(a, N.Pos{1n+k}), N.Int.mul(b, N.Pos{1n+k})) == True{} : Bool}

def le_mul_pos(a, b, k, h):
  le_mul_pos.w(a, b, k, add_of_le(a, b, h))

# ...and cancels
law le_cancel.go:
  for +a: N.Int
  for +b: N.Int
  for +k: Nat
  for +c: Nat
  for d: N.Int
  for +ed: {N.Int.sub(b, a) == d : N.Int}
  for +dk: {N.Int.mul(d, N.Pos{1n+k}) == N.Pos{c} : N.Int}
  {N.Int.is_le(a, b) == True{} : Bool}

def le_cancel.go(a, b, k, c, d, ed, dk):
  match d:
    case N.Pos{f}:
      %Equal.sym(N.Int, b, N.Int.add(a, N.Pos{f}), Equal.trans(N.Int, b, N.Int.add(a, N.Int.sub(b, a)), N.Int.add(a, N.Pos{f}),
          PI.IRing.eq(PI.IVar{1n}, PI.IAdd{PI.IVar{0n}, PI.IAdd{PI.IVar{1n}, PI.INeg{PI.IVar{0n}}}}, [a, b], {==}),
          Equal.cong(N.Int, N.Int, z => N.Int.add(a, z), N.Int.sub(b, a), N.Pos{f}, ed)))
        : {N.Int.is_le(a, _) == True{} : Bool}
      le_of_add(a, f)
    case N.Neg{f}:
      Empty.absurd({N.Int.is_le(a, b) == True{} : Bool},
        PR.pos_ne_neg(c, Nat.add(k, Nat.mul(f, 1n+k)),
          Equal.sym(N.Int, N.Neg{Nat.add(k, Nat.mul(f, 1n+k))}, N.Pos{c}, dk)))

law le_cancel.w:
  for +a: N.Int
  for +b: N.Int
  for +k: Nat
  for w: &c: Nat -> {N.Int.mul(b, N.Pos{1n+k}) == N.Int.add(N.Int.mul(a, N.Pos{1n+k}), N.Pos{c}) : N.Int}
  {N.Int.is_le(a, b) == True{} : Bool}

def le_cancel.w(a, b, k, w):
  match w:
    case (+c, e):
      le_cancel.go(a, b, k, c, N.Int.sub(b, a), {==},
        Equal.trans(N.Int, N.Int.mul(N.Int.sub(b, a), N.Pos{1n+k}),
          N.Int.sub(N.Int.mul(b, N.Pos{1n+k}), N.Int.mul(a, N.Pos{1n+k})), N.Pos{c},
          PI.IRing.eq(PI.IMul{PI.IAdd{PI.IVar{1n}, PI.INeg{PI.IVar{0n}}}, PI.IVar{2n}}, PI.IAdd{PI.IMul{PI.IVar{1n}, PI.IVar{2n}}, PI.INeg{PI.IMul{PI.IVar{0n}, PI.IVar{2n}}}}, [a, b, N.Pos{1n+k}], {==}),
          (%Equal.sym(N.Int, N.Int.mul(b, N.Pos{1n+k}), N.Int.add(N.Int.mul(a, N.Pos{1n+k}), N.Pos{c}), e)
             : {N.Int.sub(_, N.Int.mul(a, N.Pos{1n+k})) == N.Pos{c} : N.Int}
           PI.IRing.eq(PI.IAdd{PI.IAdd{PI.IVar{0n}, PI.IVar{1n}}, PI.INeg{PI.IVar{0n}}}, PI.IVar{1n}, [N.Int.mul(a, N.Pos{1n+k}), N.Pos{c}], {==}))))

law le_cancel:
  for +a: N.Int
  for +b: N.Int
  for +k: Nat
  for h: {N.Int.is_le(N.Int.mul(a, N.Pos{1n+k}), N.Int.mul(b, N.Pos{1n+k})) == True{} : Bool}
  {N.Int.is_le(a, b) == True{} : Bool}

def le_cancel(a, b, k, h):
  le_cancel.w(a, b, k, add_of_le(N.Int.mul(a, N.Pos{1n+k}), N.Int.mul(b, N.Pos{1n+k}), h))

# z + c <= z forces c == 0
law le_add_zero.go:
  for +z: N.Int
  for +c: Nat
  for +f: Nat
  for +e: {z == N.Int.add(N.Int.add(z, N.Pos{c}), N.Pos{f}) : N.Int}
  {c == 0n : Nat}

def le_add_zero.go(z, c, f, e):
  PG.nat_add_zero_l(c, f,
    PR.pos_inj(Nat.add(c, f), 0n,
      Equal.trans(N.Int, N.Pos{Nat.add(c, f)}, N.Int.sub(N.Int.add(N.Int.add(z, N.Pos{c}), N.Pos{f}), z), N.Pos{0n},
        PI.IRing.eq(PI.IAdd{PI.IVar{1n}, PI.IVar{2n}}, PI.IAdd{PI.IAdd{PI.IAdd{PI.IVar{0n}, PI.IVar{1n}}, PI.IVar{2n}}, PI.INeg{PI.IVar{0n}}}, [z, N.Pos{c}, N.Pos{f}], {==}),
        (%e : {N.Int.sub(_, z) == N.Pos{0n} : N.Int}
         PI.IRing.eq(PI.IAdd{PI.IVar{0n}, PI.INeg{PI.IVar{0n}}}, PI.IConst{N.Pos{0n}}, [z], {==})))))

law le_add_zero.w:
  for +z: N.Int
  for +c: Nat
  for w: &f: Nat -> {z == N.Int.add(N.Int.add(z, N.Pos{c}), N.Pos{f}) : N.Int}
  {c == 0n : Nat}

def le_add_zero.w(z, c, w):
  match w:
    case (+f, e):
      le_add_zero.go(z, c, f, e)

law le_add_zero:
  for +z: N.Int
  for +c: Nat
  for h: {N.Int.is_le(N.Int.add(z, N.Pos{c}), z) == True{} : Bool}
  {c == 0n : Nat}

def le_add_zero(z, c, h):
  le_add_zero.w(z, c, add_of_le(N.Int.add(z, N.Pos{c}), z, h))

# no zero divisors
law mul_eq_zero:
  for +u: N.Int
  for +d: N.Int
  for e: {N.Int.mul(u, d) == N.Pos{0n} : N.Int}
  for nz: {N.Int.is_eq(d, N.Pos{0n}) == False{} : Bool}
  {u == N.Pos{0n} : N.Int}

def mul_eq_zero(u, d, e, nz):
  match u d:
    case _ N.Pos{0n}:
      Empty.absurd({u == N.Pos{0n} : N.Int}, PD.Bool.ft(Equal.sym(Bool, True{}, False{}, nz)))
    case N.Pos{0n} N.Pos{1n+n}:
      {==}
    case N.Pos{1n+m} N.Pos{1n+n}:
      Empty.absurd({N.Pos{1n+m} == N.Pos{0n} : N.Int},
        PD.succ_ne_zero(Nat.add(n, Nat.mul(m, 1n+n)), PR.pos_inj(Nat.mul(1n+m, 1n+n), 0n, e)))
    case N.Pos{0n} N.Neg{n}:
      {==}
    case N.Pos{1n+m} N.Neg{n}:
      Empty.absurd({N.Pos{1n+m} == N.Pos{0n} : N.Int},
        PR.pos_ne_neg(0n, Nat.add(n, Nat.mul(m, 1n+n)), Equal.sym(N.Int, N.Neg{Nat.add(n, Nat.mul(m, 1n+n))}, N.Pos{0n}, e)))
    case N.Neg{m} N.Pos{1n+n}:
      Empty.absurd({N.Neg{m} == N.Pos{0n} : N.Int},
        PR.pos_ne_neg(0n, Nat.add(n, Nat.mul(m, 1n+n)), Equal.sym(N.Int, N.Neg{Nat.add(n, Nat.mul(m, 1n+n))}, N.Pos{0n}, e)))
    case N.Neg{m} N.Neg{n}:
      Empty.absurd({N.Neg{m} == N.Pos{0n} : N.Int},
        PD.succ_ne_zero(Nat.add(n, Nat.mul(m, 1n+n)), PR.pos_inj(Nat.mul(1n+m, 1n+n), 0n, e)))

# The residuals as Ints
# ---------------------
# For the line a = P / Q, b = R / S and data scaled by Lp (x = X / Lp,
# y = Y / Lp), the residual y - (a x + b) is rterm / M with M = Lp Q S.

def rterm(+p: N.Int, +q: N.Int, +r: N.Int, +s: N.Int, +lp: N.Int, +x: N.Int, +y: N.Int) -> N.Int:
  N.Int.sub(N.Int.sub(N.Int.mul(N.Int.mul(y, q), s), N.Int.mul(N.Int.mul(p, x), s)), N.Int.mul(N.Int.mul(r, q), lp))

def mden(+q: N.Int, +s: N.Int, +lp: N.Int) -> N.Int:
  N.Int.mul(N.Int.mul(lp, q), s)

# Σ rterm and Σ x rterm, from the sums
def rexp(+p: N.Int, +q: N.Int, +r: N.Int, +s: N.Int, +lp: N.Int, +st: L.Stats) -> N.Int:
  N.Int.sub(N.Int.sub(N.Int.mul(N.Int.mul(PG.ssy(st), q), s), N.Int.mul(N.Int.mul(p, PG.ssx(st)), s)),
    N.Int.mul(N.Int.mul(r, q), N.Int.mul(lp, PG.sn(st))))

def rxexp(+p: N.Int, +q: N.Int, +r: N.Int, +s: N.Int, +lp: N.Int, +st: L.Stats) -> N.Int:
  N.Int.sub(N.Int.sub(N.Int.mul(N.Int.mul(PG.ssxy(st), q), s), N.Int.mul(N.Int.mul(p, PG.ssxx(st)), s)),
    N.Int.mul(N.Int.mul(r, q), N.Int.mul(lp, PG.ssx(st))))

# Σ rterm²
def sumsq(+p: N.Int, +q: N.Int, +r: N.Int, +s: N.Int, +lp: N.Int, +l: Nat, xs: +List<N.Rat>, ys: +List<N.Rat>) -> N.Int:
  match xs ys:
    case Con{x, xt} Con{y, yt}:
      N.Int.add(PG.sq(rterm(p, q, r, s, lp, L.Stats.scale(l, x), L.Stats.scale(l, y))), sumsq(p, q, r, s, lp, l, xt, yt))
    case _ _:
      N.Pos{0n}

law rexp_step:
  for +p: N.Int
  for +q: N.Int
  for +r: N.Int
  for +s: N.Int
  for +lp: N.Int
  for +x: N.Int
  for +y: N.Int
  for st: L.Stats
  {rexp(p, q, r, s, lp, L.Stats.add(PG.pt(x, y), st)) == N.Int.add(rterm(p, q, r, s, lp, x, y), rexp(p, q, r, s, lp, st)) : N.Int}

def rexp_step(p, q, r, s, lp, x, y, st):
  match st:
    case L.Stats{+n, +sx, +sy, sxy, sxx}:
      PI.IRing.eq(PI.IAdd{PI.IAdd{PI.IMul{PI.IMul{PI.IAdd{PI.IVar{6n}, PI.IVar{9n}}, PI.IVar{1n}}, PI.IVar{3n}}, PI.INeg{PI.IMul{PI.IMul{PI.IVar{0n}, PI.IAdd{PI.IVar{5n}, PI.IVar{8n}}}, PI.IVar{3n}}}}, PI.INeg{PI.IMul{PI.IMul{PI.IVar{2n}, PI.IVar{1n}}, PI.IMul{PI.IVar{4n}, PI.IAdd{PI.IConst{N.Pos{1n}}, PI.IVar{7n}}}}}}, PI.IAdd{PI.IAdd{PI.IAdd{PI.IMul{PI.IMul{PI.IVar{6n}, PI.IVar{1n}}, PI.IVar{3n}}, PI.INeg{PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{5n}}, PI.IVar{3n}}}}, PI.INeg{PI.IMul{PI.IMul{PI.IVar{2n}, PI.IVar{1n}}, PI.IVar{4n}}}}, PI.IAdd{PI.IAdd{PI.IMul{PI.IMul{PI.IVar{9n}, PI.IVar{1n}}, PI.IVar{3n}}, PI.INeg{PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{8n}}, PI.IVar{3n}}}}, PI.INeg{PI.IMul{PI.IMul{PI.IVar{2n}, PI.IVar{1n}}, PI.IMul{PI.IVar{4n}, PI.IVar{7n}}}}}}, [p, q, r, s, lp, x, y, n, sx, sy], {==})

law rexp_zero:
  for +p: N.Int
  for +q: N.Int
  for +r: N.Int
  for +s: N.Int
  for +lp: N.Int
  {rexp(p, q, r, s, lp, L.Stats.zero()) == N.Pos{0n} : N.Int}

def rexp_zero(p, q, r, s, lp):
  PI.IRing.eq(PI.IAdd{PI.IAdd{PI.IMul{PI.IMul{PI.IConst{N.Pos{0n}}, PI.IVar{1n}}, PI.IVar{3n}}, PI.INeg{PI.IMul{PI.IMul{PI.IVar{0n}, PI.IConst{N.Pos{0n}}}, PI.IVar{3n}}}}, PI.INeg{PI.IMul{PI.IMul{PI.IVar{2n}, PI.IVar{1n}}, PI.IMul{PI.IVar{4n}, PI.IConst{N.Pos{0n}}}}}}, PI.IConst{N.Pos{0n}}, [p, q, r, s, lp], {==})

law rxexp_step:
  for +p: N.Int
  for +q: N.Int
  for +r: N.Int
  for +s: N.Int
  for +lp: N.Int
  for +x: N.Int
  for +y: N.Int
  for st: L.Stats
  {rxexp(p, q, r, s, lp, L.Stats.add(PG.pt(x, y), st))
    == N.Int.add(N.Int.mul(x, rterm(p, q, r, s, lp, x, y)), rxexp(p, q, r, s, lp, st)) : N.Int}

def rxexp_step(p, q, r, s, lp, x, y, st):
  match st:
    case L.Stats{n, +sx, sy, +sxy, +sxx}:
      PI.IRing.eq(PI.IAdd{PI.IAdd{PI.IMul{PI.IMul{PI.IAdd{PI.IMul{PI.IVar{5n}, PI.IVar{6n}}, PI.IVar{8n}}, PI.IVar{1n}}, PI.IVar{3n}}, PI.INeg{PI.IMul{PI.IMul{PI.IVar{0n}, PI.IAdd{PI.IMul{PI.IVar{5n}, PI.IVar{5n}}, PI.IVar{9n}}}, PI.IVar{3n}}}}, PI.INeg{PI.IMul{PI.IMul{PI.IVar{2n}, PI.IVar{1n}}, PI.IMul{PI.IVar{4n}, PI.IAdd{PI.IVar{5n}, PI.IVar{7n}}}}}}, PI.IAdd{PI.IMul{PI.IVar{5n}, PI.IAdd{PI.IAdd{PI.IMul{PI.IMul{PI.IVar{6n}, PI.IVar{1n}}, PI.IVar{3n}}, PI.INeg{PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{5n}}, PI.IVar{3n}}}}, PI.INeg{PI.IMul{PI.IMul{PI.IVar{2n}, PI.IVar{1n}}, PI.IVar{4n}}}}}, PI.IAdd{PI.IAdd{PI.IMul{PI.IMul{PI.IVar{8n}, PI.IVar{1n}}, PI.IVar{3n}}, PI.INeg{PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{9n}}, PI.IVar{3n}}}}, PI.INeg{PI.IMul{PI.IMul{PI.IVar{2n}, PI.IVar{1n}}, PI.IMul{PI.IVar{4n}, PI.IVar{7n}}}}}}, [p, q, r, s, lp, x, y, sx, sxy, sxx], {==})

law rxexp_zero:
  for +p: N.Int
  for +q: N.Int
  for +r: N.Int
  for +s: N.Int
  for +lp: N.Int
  {rxexp(p, q, r, s, lp, L.Stats.zero()) == N.Pos{0n} : N.Int}

def rxexp_zero(p, q, r, s, lp):
  PI.IRing.eq(PI.IAdd{PI.IAdd{PI.IMul{PI.IMul{PI.IConst{N.Pos{0n}}, PI.IVar{1n}}, PI.IVar{3n}}, PI.INeg{PI.IMul{PI.IMul{PI.IVar{0n}, PI.IConst{N.Pos{0n}}}, PI.IVar{3n}}}}, PI.INeg{PI.IMul{PI.IMul{PI.IVar{2n}, PI.IVar{1n}}, PI.IMul{PI.IVar{4n}, PI.IConst{N.Pos{0n}}}}}}, PI.IConst{N.Pos{0n}}, [p, q, r, s, lp], {==})

# The residuals as Rats
# ---------------------

law scale_den:
  for +l: Nat
  for +x: N.Rat
  for +ex: {l == Nat.mul(Laws.dnat(x), Nat.div(l, Laws.dnat(x))) : Nat}
  {N.Int.mul(Laws.num(x), N.Pos{l}) == N.Int.mul(L.Stats.scale(l, x), Laws.den(x)) : N.Int}

def scale_den(l, x, ex):
  match x:
    case N.Rat{+u, +v}:
      %Equal.sym(N.Int, N.Pos{l}, N.Pos{Nat.mul(1n+v, Nat.div(l, 1n+v))}, PG.pos_eq(l, Nat.mul(1n+v, Nat.div(l, 1n+v)), ex))
        : {N.Int.mul(u, _) == N.Int.mul(N.Int.mul(u, N.Pos{Nat.div(l, 1n+v)}), N.Pos{1n+v}) : N.Int}
      PI.IRing.eq(PI.IMul{PI.IVar{0n}, PI.IMul{PI.IVar{1n}, PI.IVar{2n}}}, PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{2n}}, PI.IVar{1n}}, [u, N.Pos{1n+v}, N.Pos{Nat.div(l, 1n+v)}], {==})

law hden:
  for +l: Nat
  for +lp: Nat
  for +hl: {l == 1n+lp : Nat}
  for +x: N.Rat
  for +ex: {l == Nat.mul(Laws.dnat(x), Nat.div(l, Laws.dnat(x))) : Nat}
  {N.Int.mul(Laws.num(x), N.Pos{1n+lp}) == N.Int.mul(L.Stats.scale(l, x), Laws.den(x)) : N.Int}

def hden(l, lp, hl, x, ex):
  %PG.pos_eq(l, 1n+lp, hl) : {N.Int.mul(Laws.num(x), _) == N.Int.mul(L.Stats.scale(l, x), Laws.den(x)) : N.Int}
  scale_den(l, x, ex)

law den_neg:
  for +r: N.Rat
  for +n: N.Int
  for +k: Nat
  for +h: {N.Int.mul(Laws.num(r), N.Pos{1n+k}) == N.Int.mul(n, Laws.den(r)) : N.Int}
  {N.Int.mul(Laws.num(N.Rat.neg(r)), N.Pos{1n+k}) == N.Int.mul(N.Int.neg(n), Laws.den(N.Rat.neg(r))) : N.Int}

def den_neg(r, n, k, h):
  match r:
    case N.Rat{+u, +d}:
      Equal.trans(N.Int, N.Int.mul(N.Int.neg(u), N.Pos{1n+k}), N.Int.neg(N.Int.mul(u, N.Pos{1n+k})),
        N.Int.mul(N.Int.neg(n), N.Pos{1n+d}),
        PI.IRing.eq(PI.IMul{PI.INeg{PI.IVar{0n}}, PI.IVar{1n}}, PI.INeg{PI.IMul{PI.IVar{0n}, PI.IVar{1n}}}, [u, N.Pos{1n+k}], {==}),
        (%Equal.sym(N.Int, N.Int.mul(u, N.Pos{1n+k}), N.Int.mul(n, N.Pos{1n+d}), h)
           : {N.Int.neg(_) == N.Int.mul(N.Int.neg(n), N.Pos{1n+d}) : N.Int}
         PI.IRing.eq(PI.INeg{PI.IMul{PI.IVar{0n}, PI.IVar{1n}}}, PI.IMul{PI.INeg{PI.IVar{0n}}, PI.IVar{1n}}, [n, N.Pos{1n+d}], {==})))

# one residual: y - (a x + b) == rterm / M
law term_den:
  for +l: Nat
  for +lp: Nat
  for +hl: {l == 1n+lp : Nat}
  for +p: N.Int
  for +qa: Nat
  for +r: N.Int
  for +sb: Nat
  for +x: N.Rat
  for +y: N.Rat
  for +ex: {l == Nat.mul(Laws.dnat(x), Nat.div(l, Laws.dnat(x))) : Nat}
  for +ey: {l == Nat.mul(Laws.dnat(y), Nat.div(l, Laws.dnat(y))) : Nat}
  Laws.Denotes(N.Rat.sub(y, Laws.at(N.Rat{p, qa}, N.Rat{r, sb}, x)),
    rterm(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, L.Stats.scale(l, x), L.Stats.scale(l, y)),
    mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp}))

def term_den(l, lp, hl, p, qa, r, sb, x, y, ex, ey):
  PR.den_trans(N.Rat.sub(y, Laws.at(N.Rat{p, qa}, N.Rat{r, sb}, x)),
    N.Int.add(N.Int.mul(L.Stats.scale(l, y), N.Pos{1n+N.Nat.mul_pred(N.Nat.mul_pred(qa, lp), sb)}),
      N.Int.mul(N.Int.neg(N.Int.add(N.Int.mul(N.Int.mul(p, L.Stats.scale(l, x)), N.Pos{1n+sb}), N.Int.mul(r, N.Pos{1n+N.Nat.mul_pred(qa, lp)}))),
        N.Pos{1n+lp})),
    N.Nat.mul_pred(lp, N.Nat.mul_pred(N.Nat.mul_pred(qa, lp), sb)),
    rterm(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, L.Stats.scale(l, x), L.Stats.scale(l, y)),
    mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp}),
    PR.den_add(y, N.Rat.neg(N.Rat.add(N.Rat.mul(N.Rat{p, qa}, x), N.Rat{r, sb})), L.Stats.scale(l, y), lp,
      N.Int.neg(N.Int.add(N.Int.mul(N.Int.mul(p, L.Stats.scale(l, x)), N.Pos{1n+sb}), N.Int.mul(r, N.Pos{1n+N.Nat.mul_pred(qa, lp)}))),
      N.Nat.mul_pred(N.Nat.mul_pred(qa, lp), sb),
      hden(l, lp, hl, y, ey),
      den_neg(N.Rat.add(N.Rat.mul(N.Rat{p, qa}, x), N.Rat{r, sb}),
        N.Int.add(N.Int.mul(N.Int.mul(p, L.Stats.scale(l, x)), N.Pos{1n+sb}), N.Int.mul(r, N.Pos{1n+N.Nat.mul_pred(qa, lp)})),
        N.Nat.mul_pred(N.Nat.mul_pred(qa, lp), sb),
        PR.den_add(N.Rat.mul(N.Rat{p, qa}, x), N.Rat{r, sb}, N.Int.mul(p, L.Stats.scale(l, x)), N.Nat.mul_pred(qa, lp), r, sb,
          PR.den_mul(N.Rat{p, qa}, x, p, qa, L.Stats.scale(l, x), lp, {==}, hden(l, lp, hl, x, ex)),
          {==}))),
    PI.IRing.eq(PI.IMul{PI.IAdd{PI.IMul{PI.IVar{0n}, PI.IMul{PI.IMul{PI.IVar{4n}, PI.IVar{5n}}, PI.IVar{6n}}}, PI.IMul{PI.INeg{PI.IAdd{PI.IMul{PI.IMul{PI.IVar{2n}, PI.IVar{1n}}, PI.IVar{6n}}, PI.IMul{PI.IVar{3n}, PI.IMul{PI.IVar{4n}, PI.IVar{5n}}}}}, PI.IVar{5n}}}, PI.IMul{PI.IMul{PI.IVar{5n}, PI.IVar{4n}}, PI.IVar{6n}}}, PI.IMul{PI.IAdd{PI.IAdd{PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{4n}}, PI.IVar{6n}}, PI.INeg{PI.IMul{PI.IMul{PI.IVar{2n}, PI.IVar{1n}}, PI.IVar{6n}}}}, PI.INeg{PI.IMul{PI.IMul{PI.IVar{3n}, PI.IVar{4n}}, PI.IVar{5n}}}}, PI.IMul{PI.IVar{5n}, PI.IMul{PI.IMul{PI.IVar{4n}, PI.IVar{5n}}, PI.IVar{6n}}}}, [L.Stats.scale(l, y), L.Stats.scale(l, x), p, r, N.Pos{1n+qa}, N.Pos{1n+lp}, N.Pos{1n+sb}], {==}))

law zero_canon:
  Laws.Canon(N.Rat.zero())

def zero_canon():
  +k => d0 => d1 => PR.of_int.canon(k, d1)

# Σ residuals == Σ rterm / M
law sumr_den:
  for +l: Nat
  for +lp: Nat
  for +hl: {l == 1n+lp : Nat}
  for +p: N.Int
  for +qa: Nat
  for +r: N.Int
  for +sb: Nat
  for xs: +List<N.Rat>
  for ys: +List<N.Rat>
  for +hx: {PG.dvb(xs, l) == True{} : Bool}
  for +hy: {PG.dvb(ys, l) == True{} : Bool}
  Laws.Denotes(Laws.sum_r(N.Rat{p, qa}, N.Rat{r, sb}, xs, ys), rexp(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, PG.rest(l, xs, ys)), mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp}))

def sumr_den(l, lp, hl, p, qa, r, sb, xs, ys, hx, hy):
  match xs ys:
    case Nil{} _:
      %Equal.sym(N.Int, rexp(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, L.Stats.zero()), N.Pos{0n}, rexp_zero(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}))
        : Laws.Denotes(N.Rat.zero(), _, mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp}))
      {==}
    case Con{x, xt} Nil{}:
      %Equal.sym(N.Int, rexp(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, L.Stats.zero()), N.Pos{0n}, rexp_zero(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}))
        : Laws.Denotes(N.Rat.zero(), _, mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp}))
      {==}
    case Con{+x, +xt} Con{+y, +yt}:
      %Equal.sym(N.Int, rexp(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, L.Stats.add(PG.pt(L.Stats.scale(l, x), L.Stats.scale(l, y)), PG.rest(l, xt, yt))),
          N.Int.add(rterm(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, L.Stats.scale(l, x), L.Stats.scale(l, y)), rexp(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, PG.rest(l, xt, yt))),
          rexp_step(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, L.Stats.scale(l, x), L.Stats.scale(l, y), PG.rest(l, xt, yt)))
        : Laws.Denotes(N.Rat.add(N.Rat.sub(y, Laws.at(N.Rat{p, qa}, N.Rat{r, sb}, x)), Laws.sum_r(N.Rat{p, qa}, N.Rat{r, sb}, xt, yt)), _, mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp}))
      PR.den_trans(N.Rat.add(N.Rat.sub(y, Laws.at(N.Rat{p, qa}, N.Rat{r, sb}, x)), Laws.sum_r(N.Rat{p, qa}, N.Rat{r, sb}, xt, yt)),
        N.Int.add(N.Int.mul(rterm(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, L.Stats.scale(l, x), L.Stats.scale(l, y)), N.Pos{1n+N.Nat.mul_pred(N.Nat.mul_pred(lp, qa), sb)}), N.Int.mul(rexp(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, PG.rest(l, xt, yt)), N.Pos{1n+N.Nat.mul_pred(N.Nat.mul_pred(lp, qa), sb)})),
        N.Nat.mul_pred(N.Nat.mul_pred(N.Nat.mul_pred(lp, qa), sb), N.Nat.mul_pred(N.Nat.mul_pred(lp, qa), sb)),
        N.Int.add(rterm(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, L.Stats.scale(l, x), L.Stats.scale(l, y)), rexp(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, PG.rest(l, xt, yt))), mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp}),
        PR.den_add(N.Rat.sub(y, Laws.at(N.Rat{p, qa}, N.Rat{r, sb}, x)), Laws.sum_r(N.Rat{p, qa}, N.Rat{r, sb}, xt, yt), rterm(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, L.Stats.scale(l, x), L.Stats.scale(l, y)), N.Nat.mul_pred(N.Nat.mul_pred(lp, qa), sb), rexp(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, PG.rest(l, xt, yt)), N.Nat.mul_pred(N.Nat.mul_pred(lp, qa), sb),
          term_den(l, lp, hl, p, qa, r, sb, x, y, PG.dvb_head(l, x, xt, hx), PG.dvb_head(l, y, yt, hy)), sumr_den(l, lp, hl, p, qa, r, sb, xt, yt, PG.dvb_tail(l, x, xt, hx), PG.dvb_tail(l, y, yt, hy))),
        PI.IRing.eq(PI.IMul{PI.IAdd{PI.IMul{PI.IVar{0n}, PI.IVar{2n}}, PI.IMul{PI.IVar{1n}, PI.IVar{2n}}}, PI.IVar{2n}}, PI.IMul{PI.IAdd{PI.IVar{0n}, PI.IVar{1n}}, PI.IMul{PI.IVar{2n}, PI.IVar{2n}}}, [rterm(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, L.Stats.scale(l, x), L.Stats.scale(l, y)), rexp(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, PG.rest(l, xt, yt)), mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp})], {==}))

# Σ x residual == Σ X rterm / (Lp M)
law sumxr_den:
  for +l: Nat
  for +lp: Nat
  for +hl: {l == 1n+lp : Nat}
  for +p: N.Int
  for +qa: Nat
  for +r: N.Int
  for +sb: Nat
  for xs: +List<N.Rat>
  for ys: +List<N.Rat>
  for +hx: {PG.dvb(xs, l) == True{} : Bool}
  for +hy: {PG.dvb(ys, l) == True{} : Bool}
  Laws.Denotes(Laws.sum_xr(N.Rat{p, qa}, N.Rat{r, sb}, xs, ys), rxexp(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, PG.rest(l, xs, ys)), N.Int.mul(N.Pos{1n+lp}, mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp})))

def sumxr_den(l, lp, hl, p, qa, r, sb, xs, ys, hx, hy):
  match xs ys:
    case Nil{} _:
      %Equal.sym(N.Int, rxexp(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, L.Stats.zero()), N.Pos{0n}, rxexp_zero(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}))
        : Laws.Denotes(N.Rat.zero(), _, N.Int.mul(N.Pos{1n+lp}, mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp})))
      {==}
    case Con{x, xt} Nil{}:
      %Equal.sym(N.Int, rxexp(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, L.Stats.zero()), N.Pos{0n}, rxexp_zero(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}))
        : Laws.Denotes(N.Rat.zero(), _, N.Int.mul(N.Pos{1n+lp}, mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp})))
      {==}
    case Con{+x, +xt} Con{+y, +yt}:
      %Equal.sym(N.Int, rxexp(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, L.Stats.add(PG.pt(L.Stats.scale(l, x), L.Stats.scale(l, y)), PG.rest(l, xt, yt))),
          N.Int.add(N.Int.mul(L.Stats.scale(l, x), rterm(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, L.Stats.scale(l, x), L.Stats.scale(l, y))), rxexp(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, PG.rest(l, xt, yt))),
          rxexp_step(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, L.Stats.scale(l, x), L.Stats.scale(l, y), PG.rest(l, xt, yt)))
        : Laws.Denotes(N.Rat.add(N.Rat.mul(x, N.Rat.sub(y, Laws.at(N.Rat{p, qa}, N.Rat{r, sb}, x))), Laws.sum_xr(N.Rat{p, qa}, N.Rat{r, sb}, xt, yt)), _, N.Int.mul(N.Pos{1n+lp}, mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp})))
      PR.den_trans(N.Rat.add(N.Rat.mul(x, N.Rat.sub(y, Laws.at(N.Rat{p, qa}, N.Rat{r, sb}, x))), Laws.sum_xr(N.Rat{p, qa}, N.Rat{r, sb}, xt, yt)),
        N.Int.add(N.Int.mul(N.Int.mul(L.Stats.scale(l, x), rterm(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, L.Stats.scale(l, x), L.Stats.scale(l, y))), N.Pos{1n+N.Nat.mul_pred(lp, N.Nat.mul_pred(N.Nat.mul_pred(lp, qa), sb))}),
          N.Int.mul(rxexp(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, PG.rest(l, xt, yt)), N.Pos{1n+N.Nat.mul_pred(lp, N.Nat.mul_pred(N.Nat.mul_pred(lp, qa), sb))})),
        N.Nat.mul_pred(N.Nat.mul_pred(lp, N.Nat.mul_pred(N.Nat.mul_pred(lp, qa), sb)), N.Nat.mul_pred(lp, N.Nat.mul_pred(N.Nat.mul_pred(lp, qa), sb))),
        N.Int.add(N.Int.mul(L.Stats.scale(l, x), rterm(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, L.Stats.scale(l, x), L.Stats.scale(l, y))), rxexp(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, PG.rest(l, xt, yt))), N.Int.mul(N.Pos{1n+lp}, mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp})),
        PR.den_add(N.Rat.mul(x, N.Rat.sub(y, Laws.at(N.Rat{p, qa}, N.Rat{r, sb}, x))), Laws.sum_xr(N.Rat{p, qa}, N.Rat{r, sb}, xt, yt), N.Int.mul(L.Stats.scale(l, x), rterm(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, L.Stats.scale(l, x), L.Stats.scale(l, y))), N.Nat.mul_pred(lp, N.Nat.mul_pred(N.Nat.mul_pred(lp, qa), sb)),
          rxexp(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, PG.rest(l, xt, yt)), N.Nat.mul_pred(lp, N.Nat.mul_pred(N.Nat.mul_pred(lp, qa), sb)),
          PR.den_mul(x, N.Rat.sub(y, Laws.at(N.Rat{p, qa}, N.Rat{r, sb}, x)), L.Stats.scale(l, x), lp, rterm(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, L.Stats.scale(l, x), L.Stats.scale(l, y)), N.Nat.mul_pred(N.Nat.mul_pred(lp, qa), sb), hden(l, lp, hl, x, PG.dvb_head(l, x, xt, hx)), term_den(l, lp, hl, p, qa, r, sb, x, y, PG.dvb_head(l, x, xt, hx), PG.dvb_head(l, y, yt, hy))),
          sumxr_den(l, lp, hl, p, qa, r, sb, xt, yt, PG.dvb_tail(l, x, xt, hx), PG.dvb_tail(l, y, yt, hy))),
        PI.IRing.eq(PI.IMul{PI.IAdd{PI.IMul{PI.IVar{0n}, PI.IVar{2n}}, PI.IMul{PI.IVar{1n}, PI.IVar{2n}}}, PI.IVar{2n}}, PI.IMul{PI.IAdd{PI.IVar{0n}, PI.IVar{1n}}, PI.IMul{PI.IVar{2n}, PI.IVar{2n}}}, [N.Int.mul(L.Stats.scale(l, x), rterm(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, L.Stats.scale(l, x), L.Stats.scale(l, y))), rxexp(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, PG.rest(l, xt, yt)), N.Int.mul(N.Pos{1n+lp}, mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp}))], {==}))

# Σ residual² == Σ rterm² / M²
law sse_den:
  for +l: Nat
  for +lp: Nat
  for +hl: {l == 1n+lp : Nat}
  for +p: N.Int
  for +qa: Nat
  for +r: N.Int
  for +sb: Nat
  for xs: +List<N.Rat>
  for ys: +List<N.Rat>
  for +hx: {PG.dvb(xs, l) == True{} : Bool}
  for +hy: {PG.dvb(ys, l) == True{} : Bool}
  Laws.Denotes(Laws.sse(N.Rat{p, qa}, N.Rat{r, sb}, xs, ys), sumsq(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, l, xs, ys), N.Int.mul(mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp}), mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp})))

def sse_den(l, lp, hl, p, qa, r, sb, xs, ys, hx, hy):
  match xs ys:
    case Nil{} _:
      {==}
    case Con{x, xt} Nil{}:
      {==}
    case Con{+x, +xt} Con{+y, +yt}:
      PR.den_trans(N.Rat.add(N.Rat.mul(N.Rat.sub(y, Laws.at(N.Rat{p, qa}, N.Rat{r, sb}, x)), N.Rat.sub(y, Laws.at(N.Rat{p, qa}, N.Rat{r, sb}, x))), Laws.sse(N.Rat{p, qa}, N.Rat{r, sb}, xt, yt)),
        N.Int.add(N.Int.mul(N.Int.mul(rterm(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, L.Stats.scale(l, x), L.Stats.scale(l, y)), rterm(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, L.Stats.scale(l, x), L.Stats.scale(l, y))), N.Pos{1n+N.Nat.mul_pred(N.Nat.mul_pred(N.Nat.mul_pred(lp, qa), sb), N.Nat.mul_pred(N.Nat.mul_pred(lp, qa), sb))}),
          N.Int.mul(sumsq(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, l, xt, yt), N.Pos{1n+N.Nat.mul_pred(N.Nat.mul_pred(N.Nat.mul_pred(lp, qa), sb), N.Nat.mul_pred(N.Nat.mul_pred(lp, qa), sb))})),
        N.Nat.mul_pred(N.Nat.mul_pred(N.Nat.mul_pred(N.Nat.mul_pred(lp, qa), sb), N.Nat.mul_pred(N.Nat.mul_pred(lp, qa), sb)), N.Nat.mul_pred(N.Nat.mul_pred(N.Nat.mul_pred(lp, qa), sb), N.Nat.mul_pred(N.Nat.mul_pred(lp, qa), sb))),
        N.Int.add(N.Int.mul(rterm(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, L.Stats.scale(l, x), L.Stats.scale(l, y)), rterm(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, L.Stats.scale(l, x), L.Stats.scale(l, y))), sumsq(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, l, xt, yt)), N.Int.mul(mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp}), mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp})),
        PR.den_add(N.Rat.mul(N.Rat.sub(y, Laws.at(N.Rat{p, qa}, N.Rat{r, sb}, x)), N.Rat.sub(y, Laws.at(N.Rat{p, qa}, N.Rat{r, sb}, x))), Laws.sse(N.Rat{p, qa}, N.Rat{r, sb}, xt, yt), N.Int.mul(rterm(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, L.Stats.scale(l, x), L.Stats.scale(l, y)), rterm(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, L.Stats.scale(l, x), L.Stats.scale(l, y))), N.Nat.mul_pred(N.Nat.mul_pred(N.Nat.mul_pred(lp, qa), sb), N.Nat.mul_pred(N.Nat.mul_pred(lp, qa), sb)),
          sumsq(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, l, xt, yt), N.Nat.mul_pred(N.Nat.mul_pred(N.Nat.mul_pred(lp, qa), sb), N.Nat.mul_pred(N.Nat.mul_pred(lp, qa), sb)),
          PR.den_mul(N.Rat.sub(y, Laws.at(N.Rat{p, qa}, N.Rat{r, sb}, x)), N.Rat.sub(y, Laws.at(N.Rat{p, qa}, N.Rat{r, sb}, x)), rterm(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, L.Stats.scale(l, x), L.Stats.scale(l, y)), N.Nat.mul_pred(N.Nat.mul_pred(lp, qa), sb), rterm(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, L.Stats.scale(l, x), L.Stats.scale(l, y)), N.Nat.mul_pred(N.Nat.mul_pred(lp, qa), sb), term_den(l, lp, hl, p, qa, r, sb, x, y, PG.dvb_head(l, x, xt, hx), PG.dvb_head(l, y, yt, hy)), term_den(l, lp, hl, p, qa, r, sb, x, y, PG.dvb_head(l, x, xt, hx), PG.dvb_head(l, y, yt, hy))),
          sse_den(l, lp, hl, p, qa, r, sb, xt, yt, PG.dvb_tail(l, x, xt, hx), PG.dvb_tail(l, y, yt, hy))),
        PI.IRing.eq(PI.IMul{PI.IAdd{PI.IMul{PI.IVar{0n}, PI.IVar{2n}}, PI.IMul{PI.IVar{1n}, PI.IVar{2n}}}, PI.IVar{2n}}, PI.IMul{PI.IAdd{PI.IVar{0n}, PI.IVar{1n}}, PI.IMul{PI.IVar{2n}, PI.IVar{2n}}}, [N.Int.mul(rterm(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, L.Stats.scale(l, x), L.Stats.scale(l, y)), rterm(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, L.Stats.scale(l, x), L.Stats.scale(l, y))), sumsq(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, l, xt, yt), N.Int.mul(mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp}), mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp}))], {==}))

law sumr_canon:
  for +a: N.Rat
  for +b: N.Rat
  for xs: +List<N.Rat>
  for ys: +List<N.Rat>
  Laws.Canon(Laws.sum_r(a, b, xs, ys))

def sumr_canon(a, b, xs, ys):
  match xs ys:
    case Nil{} _:
      zero_canon()
    case Con{x, xt} Nil{}:
      zero_canon()
    case Con{+x, +xt} Con{+y, +yt}:
      PR.add_canon(N.Rat.sub(y, Laws.at(a, b, x)), Laws.sum_r(a, b, xt, yt))

law sumxr_canon:
  for +a: N.Rat
  for +b: N.Rat
  for xs: +List<N.Rat>
  for ys: +List<N.Rat>
  Laws.Canon(Laws.sum_xr(a, b, xs, ys))

def sumxr_canon(a, b, xs, ys):
  match xs ys:
    case Nil{} _:
      zero_canon()
    case Con{x, xt} Nil{}:
      zero_canon()
    case Con{+x, +xt} Con{+y, +yt}:
      PR.add_canon(N.Rat.mul(x, N.Rat.sub(y, Laws.at(a, b, x))), Laws.sum_xr(a, b, xt, yt))

# a value denoting 0 / M with M != 0 has numerator 0
law num_zero:
  for r: N.Rat
  for +m: N.Int
  for h: Laws.Denotes(r, N.Pos{0n}, m)
  for +nz: {N.Int.is_eq(m, N.Pos{0n}) == False{} : Bool}
  {Laws.num(r) == N.Pos{0n} : N.Int}

def num_zero(r, m, h, nz):
  match r:
    case N.Rat{+u, d}:
      mul_eq_zero(u, m, h, nz)

law zero_of_num:
  for r: N.Rat
  for +h: {Laws.num(r) == N.Pos{0n} : N.Int}
  for c: Laws.Canon(r)
  {r == N.Rat.zero() : N.Rat}

def zero_of_num(r, h, c):
  match r:
    case N.Rat{+u, +d}:
      PR.canon_eq(N.Rat{u, d}, N.Rat.zero(), c, zero_canon(),
        (%Equal.sym(N.Int, u, N.Pos{0n}, h) : {N.Int.mul(_, N.Pos{1n}) == N.Int.mul(N.Pos{0n}, N.Pos{1n+d}) : N.Int}
         {==}))

# Normal equations
# ----------------

# solve's numerators, from the sums
def n1e(+st: L.Stats) -> N.Int:
  N.Int.sub(N.Int.mul(PG.sn(st), PG.ssxy(st)), N.Int.mul(PG.ssx(st), PG.ssy(st)))

def n2e(+st: L.Stats) -> N.Int:
  N.Int.sub(N.Int.mul(PG.ssy(st), PG.ssxx(st)), N.Int.mul(PG.ssx(st), PG.ssxy(st)))

# With a = n1 / D and b = n2 / (Lp D), Σ rterm == 0...
law ne_r:
  for +p: N.Int
  for +q: N.Int
  for +r: N.Int
  for +s: N.Int
  for +lp: N.Int
  for st: L.Stats
  for +ha: {N.Int.mul(p, PG.dexp(st)) == N.Int.mul(n1e(st), q) : N.Int}
  for +hb: {N.Int.mul(r, N.Int.mul(lp, PG.dexp(st))) == N.Int.mul(n2e(st), s) : N.Int}
  for +nz: {N.Int.is_eq(PG.dexp(st), N.Pos{0n}) == False{} : Bool}
  {rexp(p, q, r, s, lp, st) == N.Pos{0n} : N.Int}

def ne_r(p, q, r, s, lp, st, ha, hb, nz):
  match st:
    case L.Stats{+n, +sx, +sy, +sxy, +sxx}:
      mul_eq_zero(rexp(p, q, r, s, lp, L.Stats{n, sx, sy, sxy, sxx}), N.Int.sub(N.Int.mul(n, sxx), N.Int.mul(sx, sx)),
        Equal.trans(N.Int, N.Int.mul(rexp(p, q, r, s, lp, L.Stats{n, sx, sy, sxy, sxx}), N.Int.sub(N.Int.mul(n, sxx), N.Int.mul(sx, sx))),
          N.Int.sub(N.Int.sub(N.Int.mul(N.Int.mul(N.Int.mul(sy, q), s), N.Int.sub(N.Int.mul(n, sxx), N.Int.mul(sx, sx))),
              N.Int.mul(N.Int.mul(p, N.Int.sub(N.Int.mul(n, sxx), N.Int.mul(sx, sx))), N.Int.mul(s, sx))),
            N.Int.mul(N.Int.mul(r, N.Int.mul(lp, N.Int.sub(N.Int.mul(n, sxx), N.Int.mul(sx, sx)))), N.Int.mul(q, n))),
          N.Pos{0n},
          PI.IRing.eq(PI.IMul{PI.IAdd{PI.IAdd{PI.IMul{PI.IMul{PI.IVar{7n}, PI.IVar{1n}}, PI.IVar{3n}}, PI.INeg{PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{6n}}, PI.IVar{3n}}}}, PI.INeg{PI.IMul{PI.IMul{PI.IVar{2n}, PI.IVar{1n}}, PI.IMul{PI.IVar{4n}, PI.IVar{5n}}}}}, PI.IVar{8n}}, PI.IAdd{PI.IAdd{PI.IMul{PI.IMul{PI.IMul{PI.IVar{7n}, PI.IVar{1n}}, PI.IVar{3n}}, PI.IVar{8n}}, PI.INeg{PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{8n}}, PI.IMul{PI.IVar{3n}, PI.IVar{6n}}}}}, PI.INeg{PI.IMul{PI.IMul{PI.IVar{2n}, PI.IMul{PI.IVar{4n}, PI.IVar{8n}}}, PI.IMul{PI.IVar{1n}, PI.IVar{5n}}}}}, [p, q, r, s, lp, n, sx, sy, N.Int.sub(N.Int.mul(n, sxx), N.Int.mul(sx, sx))], {==}),
          (%Equal.sym(N.Int, N.Int.mul(p, N.Int.sub(N.Int.mul(n, sxx), N.Int.mul(sx, sx))),
               N.Int.mul(N.Int.sub(N.Int.mul(n, sxy), N.Int.mul(sx, sy)), q), ha)
             : {N.Int.sub(N.Int.sub(N.Int.mul(N.Int.mul(N.Int.mul(sy, q), s), N.Int.sub(N.Int.mul(n, sxx), N.Int.mul(sx, sx))),
                   N.Int.mul(_, N.Int.mul(s, sx))),
                 N.Int.mul(N.Int.mul(r, N.Int.mul(lp, N.Int.sub(N.Int.mul(n, sxx), N.Int.mul(sx, sx)))), N.Int.mul(q, n))) == N.Pos{0n} : N.Int}
           %Equal.sym(N.Int, N.Int.mul(r, N.Int.mul(lp, N.Int.sub(N.Int.mul(n, sxx), N.Int.mul(sx, sx)))),
               N.Int.mul(N.Int.sub(N.Int.mul(sy, sxx), N.Int.mul(sx, sxy)), s), hb)
             : {N.Int.sub(N.Int.sub(N.Int.mul(N.Int.mul(N.Int.mul(sy, q), s), N.Int.sub(N.Int.mul(n, sxx), N.Int.mul(sx, sx))),
                   N.Int.mul(N.Int.mul(N.Int.sub(N.Int.mul(n, sxy), N.Int.mul(sx, sy)), q), N.Int.mul(s, sx))),
                 N.Int.mul(_, N.Int.mul(q, n))) == N.Pos{0n} : N.Int}
           PI.IRing.eq(PI.IAdd{PI.IAdd{PI.IMul{PI.IMul{PI.IMul{PI.IVar{4n}, PI.IVar{0n}}, PI.IVar{1n}}, PI.IAdd{PI.IMul{PI.IVar{2n}, PI.IVar{6n}}, PI.INeg{PI.IMul{PI.IVar{3n}, PI.IVar{3n}}}}}, PI.INeg{PI.IMul{PI.IMul{PI.IAdd{PI.IMul{PI.IVar{2n}, PI.IVar{5n}}, PI.INeg{PI.IMul{PI.IVar{3n}, PI.IVar{4n}}}}, PI.IVar{0n}}, PI.IMul{PI.IVar{1n}, PI.IVar{3n}}}}}, PI.INeg{PI.IMul{PI.IMul{PI.IAdd{PI.IMul{PI.IVar{4n}, PI.IVar{6n}}, PI.INeg{PI.IMul{PI.IVar{3n}, PI.IVar{5n}}}}, PI.IVar{1n}}, PI.IMul{PI.IVar{0n}, PI.IVar{2n}}}}}, PI.IConst{N.Pos{0n}}, [q, s, n, sx, sy, sxy, sxx], {==}))),
        nz)

# ...and Σ x rterm == 0
law ne_rx:
  for +p: N.Int
  for +q: N.Int
  for +r: N.Int
  for +s: N.Int
  for +lp: N.Int
  for st: L.Stats
  for +ha: {N.Int.mul(p, PG.dexp(st)) == N.Int.mul(n1e(st), q) : N.Int}
  for +hb: {N.Int.mul(r, N.Int.mul(lp, PG.dexp(st))) == N.Int.mul(n2e(st), s) : N.Int}
  for +nz: {N.Int.is_eq(PG.dexp(st), N.Pos{0n}) == False{} : Bool}
  {rxexp(p, q, r, s, lp, st) == N.Pos{0n} : N.Int}

def ne_rx(p, q, r, s, lp, st, ha, hb, nz):
  match st:
    case L.Stats{+n, +sx, +sy, +sxy, +sxx}:
      mul_eq_zero(rxexp(p, q, r, s, lp, L.Stats{n, sx, sy, sxy, sxx}), N.Int.sub(N.Int.mul(n, sxx), N.Int.mul(sx, sx)),
        Equal.trans(N.Int, N.Int.mul(rxexp(p, q, r, s, lp, L.Stats{n, sx, sy, sxy, sxx}), N.Int.sub(N.Int.mul(n, sxx), N.Int.mul(sx, sx))),
          N.Int.sub(N.Int.sub(N.Int.mul(N.Int.mul(N.Int.mul(sxy, q), s), N.Int.sub(N.Int.mul(n, sxx), N.Int.mul(sx, sx))),
              N.Int.mul(N.Int.mul(p, N.Int.sub(N.Int.mul(n, sxx), N.Int.mul(sx, sx))), N.Int.mul(s, sxx))),
            N.Int.mul(N.Int.mul(r, N.Int.mul(lp, N.Int.sub(N.Int.mul(n, sxx), N.Int.mul(sx, sx)))), N.Int.mul(q, sx))),
          N.Pos{0n},
          PI.IRing.eq(PI.IMul{PI.IAdd{PI.IAdd{PI.IMul{PI.IMul{PI.IVar{6n}, PI.IVar{1n}}, PI.IVar{3n}}, PI.INeg{PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{7n}}, PI.IVar{3n}}}}, PI.INeg{PI.IMul{PI.IMul{PI.IVar{2n}, PI.IVar{1n}}, PI.IMul{PI.IVar{4n}, PI.IVar{5n}}}}}, PI.IVar{8n}}, PI.IAdd{PI.IAdd{PI.IMul{PI.IMul{PI.IMul{PI.IVar{6n}, PI.IVar{1n}}, PI.IVar{3n}}, PI.IVar{8n}}, PI.INeg{PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{8n}}, PI.IMul{PI.IVar{3n}, PI.IVar{7n}}}}}, PI.INeg{PI.IMul{PI.IMul{PI.IVar{2n}, PI.IMul{PI.IVar{4n}, PI.IVar{8n}}}, PI.IMul{PI.IVar{1n}, PI.IVar{5n}}}}}, [p, q, r, s, lp, sx, sxy, sxx, N.Int.sub(N.Int.mul(n, sxx), N.Int.mul(sx, sx))], {==}),
          (%Equal.sym(N.Int, N.Int.mul(p, N.Int.sub(N.Int.mul(n, sxx), N.Int.mul(sx, sx))),
               N.Int.mul(N.Int.sub(N.Int.mul(n, sxy), N.Int.mul(sx, sy)), q), ha)
             : {N.Int.sub(N.Int.sub(N.Int.mul(N.Int.mul(N.Int.mul(sxy, q), s), N.Int.sub(N.Int.mul(n, sxx), N.Int.mul(sx, sx))),
                   N.Int.mul(_, N.Int.mul(s, sxx))),
                 N.Int.mul(N.Int.mul(r, N.Int.mul(lp, N.Int.sub(N.Int.mul(n, sxx), N.Int.mul(sx, sx)))), N.Int.mul(q, sx))) == N.Pos{0n} : N.Int}
           %Equal.sym(N.Int, N.Int.mul(r, N.Int.mul(lp, N.Int.sub(N.Int.mul(n, sxx), N.Int.mul(sx, sx)))),
               N.Int.mul(N.Int.sub(N.Int.mul(sy, sxx), N.Int.mul(sx, sxy)), s), hb)
             : {N.Int.sub(N.Int.sub(N.Int.mul(N.Int.mul(N.Int.mul(sxy, q), s), N.Int.sub(N.Int.mul(n, sxx), N.Int.mul(sx, sx))),
                   N.Int.mul(N.Int.mul(N.Int.sub(N.Int.mul(n, sxy), N.Int.mul(sx, sy)), q), N.Int.mul(s, sxx))),
                 N.Int.mul(_, N.Int.mul(q, sx))) == N.Pos{0n} : N.Int}
           PI.IRing.eq(PI.IAdd{PI.IAdd{PI.IMul{PI.IMul{PI.IMul{PI.IVar{5n}, PI.IVar{0n}}, PI.IVar{1n}}, PI.IAdd{PI.IMul{PI.IVar{2n}, PI.IVar{6n}}, PI.INeg{PI.IMul{PI.IVar{3n}, PI.IVar{3n}}}}}, PI.INeg{PI.IMul{PI.IMul{PI.IAdd{PI.IMul{PI.IVar{2n}, PI.IVar{5n}}, PI.INeg{PI.IMul{PI.IVar{3n}, PI.IVar{4n}}}}, PI.IVar{0n}}, PI.IMul{PI.IVar{1n}, PI.IVar{6n}}}}}, PI.INeg{PI.IMul{PI.IMul{PI.IAdd{PI.IMul{PI.IVar{4n}, PI.IVar{6n}}, PI.INeg{PI.IMul{PI.IVar{3n}, PI.IVar{5n}}}}, PI.IVar{1n}}, PI.IMul{PI.IVar{0n}, PI.IVar{3n}}}}}, PI.IConst{N.Pos{0n}}, [q, s, n, sx, sy, sxy, sxx], {==}))),
        nz)

# Through the origin, a = Σxy / Σx² and b = 0 give Σ x rterm == 0.
law ne_rx_origin:
  for +p: N.Int
  for +q: N.Int
  for +lp: N.Int
  for st: L.Stats
  for +ha: {N.Int.mul(p, PG.ssxx(st)) == N.Int.mul(PG.ssxy(st), q) : N.Int}
  for +nz: {N.Int.is_eq(PG.ssxx(st), N.Pos{0n}) == False{} : Bool}
  {rxexp(p, q, N.Pos{0n}, N.Pos{1n}, lp, st) == N.Pos{0n} : N.Int}

def ne_rx_origin(p, q, lp, st, ha, nz):
  match st:
    case L.Stats{n, +sx, sy, +sxy, +sxx}:
      Equal.trans(N.Int, rxexp(p, q, N.Pos{0n}, N.Pos{1n}, lp, L.Stats{n, sx, sy, sxy, sxx}),
        N.Int.sub(N.Int.mul(sxy, q), N.Int.mul(p, sxx)), N.Pos{0n},
        PI.IRing.eq(PI.IAdd{PI.IAdd{PI.IMul{PI.IMul{PI.IVar{4n}, PI.IVar{1n}}, PI.IConst{N.Pos{1n}}}, PI.INeg{PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{5n}}, PI.IConst{N.Pos{1n}}}}}, PI.INeg{PI.IMul{PI.IMul{PI.IConst{N.Pos{0n}}, PI.IVar{1n}}, PI.IMul{PI.IVar{2n}, PI.IVar{3n}}}}}, PI.IAdd{PI.IMul{PI.IVar{4n}, PI.IVar{1n}}, PI.INeg{PI.IMul{PI.IVar{0n}, PI.IVar{5n}}}}, [p, q, lp, sx, sxy, sxx], {==}),
        (%Equal.sym(N.Int, N.Int.mul(p, sxx), N.Int.mul(sxy, q), ha)
           : {N.Int.sub(N.Int.mul(sxy, q), _) == N.Pos{0n} : N.Int}
         PI.IRing.eq(PI.IAdd{PI.IMul{PI.IVar{1n}, PI.IVar{0n}}, PI.INeg{PI.IMul{PI.IVar{1n}, PI.IVar{0n}}}}, PI.IConst{N.Pos{0n}}, [q, sxy], {==})))

# Inverting fit
# -------------

def rdone(r: Result<L.FitError, L.LinearRegression>) -> Type:
  match r:
    case Done{v}:
      Unit
    case Fail{e}:
      Empty

law fail_ne_done:
  for +er: L.FitError
  for +m: L.LinearRegression
  for e: {Fail{er} == Done{m} : Result<L.FitError, L.LinearRegression>}
  Empty

def fail_ne_done(er, m, e):
  %Equal.sym(Result<L.FitError, L.LinearRegression>, Fail{er}, Done{m}, e) : rdone(_)
  Unit{}

def isnone(m: Maybe<N.Rat>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{v}:
      Empty

def unsome(m: Maybe<N.Rat>, +d: N.Rat) -> N.Rat:
  match m:
    case None{}:
      d
    case Some{v}:
      v

law some_inj:
  for +a: N.Rat
  for +b: N.Rat
  for e: {Some{a} == Some{b} : Maybe<N.Rat>}
  {a == b : N.Rat}

def some_inj(a, b, e):
  Equal.cong(Maybe<N.Rat>, N.Rat, z => unsome(z, a), Some{a}, Some{b}, e)

law none_ne_some:
  for +r: N.Rat
  for e: {None{} == Some{r} : Maybe<N.Rat>}
  Empty

def none_ne_some(r, e):
  %e : isnone(_)
  Unit{}

# make(n, d) == Some r means r == n / d with d != 0
law make_den:
  for +n: N.Int
  for +d: N.Int
  for +r: N.Rat
  for e: {N.Rat.make(n, d) == Some{r} : Maybe<N.Rat>}
  Laws.Denotes(r, n, d)

def make_den(n, d, r, e):
  match d:
    case N.Pos{0n}:
      Empty.absurd(Laws.Denotes(r, n, N.Pos{0n}), none_ne_some(r, e))
    case N.Pos{1n+p}:
      %some_inj(N.Rat.reduce(n, p), r, e) : Laws.Denotes(_, n, N.Pos{1n+p})
      PR.cd_den(N.Rat.reduce(n, p), n, N.Pos{1n+p}, PR.reduce_ok(n, p))
    case N.Neg{p}:
      %some_inj(N.Rat.reduce(N.Int.neg(n), p), r, e) : Laws.Denotes(_, n, N.Neg{p})
      PR.cd_den(N.Rat.reduce(N.Int.neg(n), p), n, N.Neg{p}, PR.make_ok.neg(n, p, PR.reduce_ok(N.Int.neg(n), p)))

law make_nz:
  for +n: N.Int
  for +d: N.Int
  for +r: N.Rat
  for e: {N.Rat.make(n, d) == Some{r} : Maybe<N.Rat>}
  {N.Int.is_eq(d, N.Pos{0n}) == False{} : Bool}

def make_nz(n, d, r, e):
  match d:
    case N.Pos{0n}:
      Empty.absurd({True{} == False{} : Bool}, none_ne_some(r, e))
    case N.Pos{1n+p}:
      {==}
    case N.Neg{p}:
      {==}

def res_coef(r: Result<L.FitError, L.LinearRegression>) -> N.Rat:
  match r:
    case Done{L.LinearRegression{fi, c, i}}:
      c
    case Fail{e}:
      N.Rat.zero()

def res_icpt(r: Result<L.FitError, L.LinearRegression>) -> N.Rat:
  match r:
    case Done{L.LinearRegression{fi, c, i}}:
      i
    case Fail{e}:
      N.Rat.zero()

law done_inv:
  for +fi: Bool
  for ma: Maybe<N.Rat>
  for mb: Maybe<N.Rat>
  for +a: N.Rat
  for +b: N.Rat
  for +ok: {L.LinearRegression.done(fi, ma, mb) == Done{L.LinearRegression{fi, a, b}} : Result<L.FitError, L.LinearRegression>}
  {ma == Some{a} : Maybe<N.Rat>} & {mb == Some{b} : Maybe<N.Rat>}

def done_inv(fi, ma, mb, a, b, ok):
  match ma mb:
    case None{} None{}:
      Empty.absurd({None{} == Some{a} : Maybe<N.Rat>} & {None{} == Some{b} : Maybe<N.Rat>},
        fail_ne_done(L.Degenerate{}, L.LinearRegression{fi, a, b}, ok))
    case None{} Some{v}:
      Empty.absurd({None{} == Some{a} : Maybe<N.Rat>} & {Some{v} == Some{b} : Maybe<N.Rat>},
        fail_ne_done(L.Degenerate{}, L.LinearRegression{fi, a, b}, ok))
    case Some{u} None{}:
      Empty.absurd({Some{u} == Some{a} : Maybe<N.Rat>} & {None{} == Some{b} : Maybe<N.Rat>},
        fail_ne_done(L.Degenerate{}, L.LinearRegression{fi, a, b}, ok))
    case Some{+u} Some{+v}:
      (Equal.cong(N.Rat, Maybe<N.Rat>, z => Some{z}, u, a,
         Equal.cong(Result<L.FitError, L.LinearRegression>, N.Rat, z => res_coef(z), Done{L.LinearRegression{fi, u, v}}, Done{L.LinearRegression{fi, a, b}}, ok)),
       Equal.cong(N.Rat, Maybe<N.Rat>, z => Some{z}, v, b,
         Equal.cong(Result<L.FitError, L.LinearRegression>, N.Rat, z => res_icpt(z), Done{L.LinearRegression{fi, u, v}}, Done{L.LinearRegression{fi, a, b}}, ok)))

law solve_inv.h:
  for +l: Nat
  for +n1: N.Int
  for +d: N.Int
  for +n2: N.Int
  for +a: N.Rat
  for +b: N.Rat
  for +ea: {N.Rat.make(n1, d) == Some{a} : Maybe<N.Rat>}
  for +eb: {N.Rat.make(n2, N.Int.mul(N.Pos{l}, d)) == Some{b} : Maybe<N.Rat>}
  Laws.Denotes(a, n1, d) & Laws.Denotes(b, n2, N.Int.mul(N.Pos{l}, d)) & {N.Int.is_eq(d, N.Pos{0n}) == False{} : Bool}

def solve_inv.h(l, n1, d, n2, a, b, ea, eb):
  (make_den(n1, d, a, ea), (make_den(n2, N.Int.mul(N.Pos{l}, d), b, eb), make_nz(n1, d, a, ea)))

law solve_inv.go:
  for +l: Nat
  for +n1: N.Int
  for +d: N.Int
  for +n2: N.Int
  for +a: N.Rat
  for +b: N.Rat
  for pr: {N.Rat.make(n1, d) == Some{a} : Maybe<N.Rat>} & {N.Rat.make(n2, N.Int.mul(N.Pos{l}, d)) == Some{b} : Maybe<N.Rat>}
  Laws.Denotes(a, n1, d) & Laws.Denotes(b, n2, N.Int.mul(N.Pos{l}, d)) & {N.Int.is_eq(d, N.Pos{0n}) == False{} : Bool}

def solve_inv.go(l, n1, d, n2, a, b, pr):
  match pr:
    case (ea, eb):
      solve_inv.h(l, n1, d, n2, a, b, ea, eb)

# solve's answer is n1 / D and n2 / (l D), with D != 0
law solve_inv:
  for +l: Nat
  for s: L.Stats
  for +a: N.Rat
  for +b: N.Rat
  for +ok: {L.LinearRegression.solve(l, s) == Done{L.LinearRegression{True{}, a, b}} : Result<L.FitError, L.LinearRegression>}
  Laws.Denotes(a, n1e(s), PG.dexp(s)) & Laws.Denotes(b, n2e(s), N.Int.mul(N.Pos{l}, PG.dexp(s)))
    & {N.Int.is_eq(PG.dexp(s), N.Pos{0n}) == False{} : Bool}

def solve_inv(l, s, a, b, ok):
  match s:
    case L.Stats{+n, +sx, +sy, +sxy, +sxx}:
      solve_inv.go(l, N.Int.sub(N.Int.mul(n, sxy), N.Int.mul(sx, sy)), N.Int.sub(N.Int.mul(n, sxx), N.Int.mul(sx, sx)),
        N.Int.sub(N.Int.mul(sy, sxx), N.Int.mul(sx, sxy)), a, b,
        done_inv(True{}, N.Rat.make(N.Int.sub(N.Int.mul(n, sxy), N.Int.mul(sx, sy)), N.Int.sub(N.Int.mul(n, sxx), N.Int.mul(sx, sx))),
          N.Rat.make(N.Int.sub(N.Int.mul(sy, sxx), N.Int.mul(sx, sxy)), N.Int.mul(N.Pos{l}, N.Int.sub(N.Int.mul(n, sxx), N.Int.mul(sx, sx)))),
          a, b, ok))

law solve_origin_inv.h:
  for +n: N.Int
  for +d: N.Int
  for +a: N.Rat
  for +b: N.Rat
  for +ea: {N.Rat.make(n, d) == Some{a} : Maybe<N.Rat>}
  for +eb: {Some{N.Rat.zero()} == Some{b} : Maybe<N.Rat>}
  Laws.Denotes(a, n, d) & {b == N.Rat.zero() : N.Rat} & {N.Int.is_eq(d, N.Pos{0n}) == False{} : Bool}

def solve_origin_inv.h(n, d, a, b, ea, eb):
  (make_den(n, d, a, ea), (Equal.sym(N.Rat, N.Rat.zero(), b, some_inj(N.Rat.zero(), b, eb)), make_nz(n, d, a, ea)))

law solve_origin_inv.go:
  for +n: N.Int
  for +d: N.Int
  for +a: N.Rat
  for +b: N.Rat
  for pr: {N.Rat.make(n, d) == Some{a} : Maybe<N.Rat>} & {Some{N.Rat.zero()} == Some{b} : Maybe<N.Rat>}
  Laws.Denotes(a, n, d) & {b == N.Rat.zero() : N.Rat} & {N.Int.is_eq(d, N.Pos{0n}) == False{} : Bool}

def solve_origin_inv.go(n, d, a, b, pr):
  match pr:
    case (ea, eb):
      solve_origin_inv.h(n, d, a, b, ea, eb)

law solve_origin_inv:
  for s: L.Stats
  for +a: N.Rat
  for +b: N.Rat
  for +ok: {L.LinearRegression.solve_origin(s) == Done{L.LinearRegression{False{}, a, b}} : Result<L.FitError, L.LinearRegression>}
  Laws.Denotes(a, PG.ssxy(s), PG.ssxx(s)) & {b == N.Rat.zero() : N.Rat} & {N.Int.is_eq(PG.ssxx(s), N.Pos{0n}) == False{} : Bool}

def solve_origin_inv(s, a, b, ok):
  match s:
    case L.Stats{n, sx, sy, +sxy, +sxx}:
      solve_origin_inv.go(sxy, sxx, a, b, done_inv(False{}, N.Rat.make(sxy, sxx), Some{N.Rat.zero()}, a, b, ok))

law fit_inv.go2:
  for +k: Nat
  for +fi: Bool
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +m: L.LinearRegression
  for +ok: {L.LinearRegression.fit.within(k, fi, x <> xt, y <> yt) == Done{m} : Result<L.FitError, L.LinearRegression>}
  for +len: {List.length(&2, N.Rat, xt) == List.length(&2, N.Rat, yt) : Nat}
  for c: Bool
  for +ec: {Laws.fit_fits(k, x <> xt, y <> yt) == c : Bool}
  {List.length(&2, N.Rat, xt) == List.length(&2, N.Rat, yt) : Nat}
    & {Laws.fit_fits(k, x <> xt, y <> yt) == True{} : Bool}
    & {L.LinearRegression.fit.stats(fi, PZ.lv(x <> xt, y <> yt), PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)) == Done{m} : Result<L.FitError, L.LinearRegression>}

def fit_inv.go2(k, fi, x, xt, y, yt, m, ok, len, c, ec):
  match c:
    case False{}:
      Empty.absurd({List.length(&2, N.Rat, xt) == List.length(&2, N.Rat, yt) : Nat}
    & {Laws.fit_fits(k, x <> xt, y <> yt) == True{} : Bool}
    & {L.LinearRegression.fit.stats(fi, PZ.lv(x <> xt, y <> yt), PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)) == Done{m} : Result<L.FitError, L.LinearRegression>},
        fail_ne_done(L.TooLarge{}, m,
          Equal.trans(Result<L.FitError, L.LinearRegression>, Fail{L.TooLarge{}}, L.LinearRegression.fit.within(k, fi, x <> xt, y <> yt), Done{m},
            Equal.sym(Result<L.FitError, L.LinearRegression>, L.LinearRegression.fit.within(k, fi, x <> xt, y <> yt), Fail{L.TooLarge{}},
              PZ.fit_too_large(k, fi, x, xt, y, yt, len, ec)),
            ok)))
    case True{}:
      (len, (ec, Equal.trans(Result<L.FitError, L.LinearRegression>, L.LinearRegression.fit.stats(fi, PZ.lv(x <> xt, y <> yt), PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), L.LinearRegression.fit.within(k, fi, x <> xt, y <> yt), Done{m},
        Equal.sym(Result<L.FitError, L.LinearRegression>, L.LinearRegression.fit.within(k, fi, x <> xt, y <> yt), L.LinearRegression.fit.stats(fi, PZ.lv(x <> xt, y <> yt), PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)),
          PG.fit_small(k, fi, x, xt, y, yt, len, ec)),
        ok)))

law fit_inv.go:
  for +k: Nat
  for +fi: Bool
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +m: L.LinearRegression
  for +ok: {L.LinearRegression.fit.within(k, fi, x <> xt, y <> yt) == Done{m} : Result<L.FitError, L.LinearRegression>}
  for b: Bool
  for +eb: {Nat.is_eq(List.length(&2, N.Rat, xt), List.length(&2, N.Rat, yt)) == b : Bool}
  {List.length(&2, N.Rat, xt) == List.length(&2, N.Rat, yt) : Nat}
    & {Laws.fit_fits(k, x <> xt, y <> yt) == True{} : Bool}
    & {L.LinearRegression.fit.stats(fi, PZ.lv(x <> xt, y <> yt), PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)) == Done{m} : Result<L.FitError, L.LinearRegression>}

def fit_inv.go(k, fi, x, xt, y, yt, m, ok, b, eb):
  match b:
    case False{}:
      Empty.absurd({List.length(&2, N.Rat, xt) == List.length(&2, N.Rat, yt) : Nat}
    & {Laws.fit_fits(k, x <> xt, y <> yt) == True{} : Bool}
    & {L.LinearRegression.fit.stats(fi, PZ.lv(x <> xt, y <> yt), PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)) == Done{m} : Result<L.FitError, L.LinearRegression>},
        fail_ne_done(L.LengthMismatch{}, m,
          Equal.trans(Result<L.FitError, L.LinearRegression>, Fail{L.LengthMismatch{}}, L.LinearRegression.fit.within(k, fi, x <> xt, y <> yt), Done{m},
            Equal.sym(Result<L.FitError, L.LinearRegression>, L.LinearRegression.fit.within(k, fi, x <> xt, y <> yt), Fail{L.LengthMismatch{}},
              (%Equal.sym(Bool, Nat.is_eq(List.length(&2, N.Rat, xt), List.length(&2, N.Rat, yt)), False{}, eb)
                 : {L.LinearRegression.fit.sizes(k, fi, _, x <> xt, y <> yt) == Fail{L.LengthMismatch{}} : Result<L.FitError, L.LinearRegression>}
               {==})),
            ok)))
    case True{}:
      fit_inv.go2(k, fi, x, xt, y, yt, m, ok, PG.nat_eq_true(List.length(&2, N.Rat, xt), List.length(&2, N.Rat, yt), eb),
        Laws.fit_fits(k, x <> xt, y <> yt), {==})

# A fitted model came from equal lengths, the size limit, and solving the sums.
law fit_inv:
  for +k: Nat
  for +fi: Bool
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +m: L.LinearRegression
  for +ok: {L.LinearRegression.fit.within(k, fi, x <> xt, y <> yt) == Done{m} : Result<L.FitError, L.LinearRegression>}
  {List.length(&2, N.Rat, xt) == List.length(&2, N.Rat, yt) : Nat}
    & {Laws.fit_fits(k, x <> xt, y <> yt) == True{} : Bool}
    & {L.LinearRegression.fit.stats(fi, PZ.lv(x <> xt, y <> yt), PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)) == Done{m} : Result<L.FitError, L.LinearRegression>}

def fit_inv(k, fi, x, xt, y, yt, m, ok):
  fit_inv.go(k, fi, x, xt, y, yt, m, ok, Nat.is_eq(List.length(&2, N.Rat, xt), List.length(&2, N.Rat, yt)), {==})

# The normal equations
# --------------------

law normal_eq.f:
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +p: N.Int
  for +qa: Nat
  for +r: N.Int
  for +sb: Nat
  for +lp: Nat
  for +hl: {PZ.lv(x <> xt, y <> yt) == 1n+lp : Nat}
  for +ha: {N.Int.mul(p, PG.dexp(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt))) == N.Int.mul(n1e(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{1n+qa}) : N.Int}
  for +hb: {N.Int.mul(r, N.Int.mul(N.Pos{1n+lp}, PG.dexp(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)))) == N.Int.mul(n2e(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{1n+sb}) : N.Int}
  for +nz: {N.Int.is_eq(PG.dexp(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{0n}) == False{} : Bool}
  {Laws.sum_r(N.Rat{p, qa}, N.Rat{r, sb}, x <> xt, y <> yt) == N.Rat.zero() : N.Rat} & {Laws.sum_xr(N.Rat{p, qa}, N.Rat{r, sb}, x <> xt, y <> yt) == N.Rat.zero() : N.Rat}

def normal_eq.f(x, xt, y, yt, p, qa, r, sb, lp, hl, ha, hb, nz):
  (zero_of_num(Laws.sum_r(N.Rat{p, qa}, N.Rat{r, sb}, x <> xt, y <> yt),
     num_zero(Laws.sum_r(N.Rat{p, qa}, N.Rat{r, sb}, x <> xt, y <> yt), mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp}),
       (%ne_r(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt), ha, hb, nz) : Laws.Denotes(Laws.sum_r(N.Rat{p, qa}, N.Rat{r, sb}, x <> xt, y <> yt), _, mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp}))
        sumr_den(PZ.lv(x <> xt, y <> yt), lp, hl, p, qa, r, sb, x <> xt, y <> yt, PG.dvb_xs(x <> xt, y <> yt), PG.dvb_ys(x <> xt, y <> yt))),
       {==}),
     sumr_canon(N.Rat{p, qa}, N.Rat{r, sb}, x <> xt, y <> yt)),
   zero_of_num(Laws.sum_xr(N.Rat{p, qa}, N.Rat{r, sb}, x <> xt, y <> yt),
     num_zero(Laws.sum_xr(N.Rat{p, qa}, N.Rat{r, sb}, x <> xt, y <> yt), N.Int.mul(N.Pos{1n+lp}, mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp})),
       (%ne_rx(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt), ha, hb, nz) : Laws.Denotes(Laws.sum_xr(N.Rat{p, qa}, N.Rat{r, sb}, x <> xt, y <> yt), _, N.Int.mul(N.Pos{1n+lp}, mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp})))
        sumxr_den(PZ.lv(x <> xt, y <> yt), lp, hl, p, qa, r, sb, x <> xt, y <> yt, PG.dvb_xs(x <> xt, y <> yt), PG.dvb_ys(x <> xt, y <> yt))),
       {==}),
     sumxr_canon(N.Rat{p, qa}, N.Rat{r, sb}, x <> xt, y <> yt)))

law normal_eq.s:
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +p: N.Int
  for +qa: Nat
  for +r: N.Int
  for +sb: Nat
  for +lp: Nat
  for +hl: {PZ.lv(x <> xt, y <> yt) == 1n+lp : Nat}
  for tr: Laws.Denotes(N.Rat{p, qa}, n1e(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), PG.dexp(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)))
    & Laws.Denotes(N.Rat{r, sb}, n2e(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Int.mul(N.Pos{PZ.lv(x <> xt, y <> yt)}, PG.dexp(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt))))
    & {N.Int.is_eq(PG.dexp(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{0n}) == False{} : Bool}
  {Laws.sum_r(N.Rat{p, qa}, N.Rat{r, sb}, x <> xt, y <> yt) == N.Rat.zero() : N.Rat} & {Laws.sum_xr(N.Rat{p, qa}, N.Rat{r, sb}, x <> xt, y <> yt) == N.Rat.zero() : N.Rat}

def normal_eq.s(x, xt, y, yt, p, qa, r, sb, lp, hl, tr):
  match tr:
    case (da, (db, nz)):
      normal_eq.f(x, xt, y, yt, p, qa, r, sb, lp, hl, da,
        (%hl : {N.Int.mul(r, N.Int.mul(N.Pos{_}, PG.dexp(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)))) == N.Int.mul(n2e(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{1n+sb}) : N.Int}
         db),
        nz)

law normal_eq.k:
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +p: N.Int
  for +qa: Nat
  for +r: N.Int
  for +sb: Nat
  for +ok2: {L.LinearRegression.fit.stats(True{}, PZ.lv(x <> xt, y <> yt), PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)) == Done{L.LinearRegression{True{}, N.Rat{p, qa}, N.Rat{r, sb}}} : Result<L.FitError, L.LinearRegression>}
  for +lp: Nat
  for +hl: {PZ.lv(x <> xt, y <> yt) == 1n+lp : Nat}
  {Laws.sum_r(N.Rat{p, qa}, N.Rat{r, sb}, x <> xt, y <> yt) == N.Rat.zero() : N.Rat} & {Laws.sum_xr(N.Rat{p, qa}, N.Rat{r, sb}, x <> xt, y <> yt) == N.Rat.zero() : N.Rat}

def normal_eq.k(x, xt, y, yt, p, qa, r, sb, ok2, lp, hl):
  normal_eq.s(x, xt, y, yt, p, qa, r, sb, lp, hl, solve_inv(PZ.lv(x <> xt, y <> yt), PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt), N.Rat{p, qa}, N.Rat{r, sb}, ok2))

law normal_eq.j:
  for +k: Nat
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +p: N.Int
  for +qa: Nat
  for +r: N.Int
  for +sb: Nat
  for +ok2: {L.LinearRegression.fit.stats(True{}, PZ.lv(x <> xt, y <> yt), PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)) == Done{L.LinearRegression{True{}, N.Rat{p, qa}, N.Rat{r, sb}}} : Result<L.FitError, L.LinearRegression>}
  for w: PD.LeW(1n, PZ.lv(x <> xt, y <> yt))
  {Laws.sum_r(N.Rat{p, qa}, N.Rat{r, sb}, x <> xt, y <> yt) == N.Rat.zero() : N.Rat} & {Laws.sum_xr(N.Rat{p, qa}, N.Rat{r, sb}, x <> xt, y <> yt) == N.Rat.zero() : N.Rat}

def normal_eq.j(k, x, xt, y, yt, p, qa, r, sb, ok2, w):
  match w:
    case (+lp, hl):
      normal_eq.k(x, xt, y, yt, p, qa, r, sb, ok2, lp, hl)

law normal_eq.i:
  for +k: Nat
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +p: N.Int
  for +qa: Nat
  for +r: N.Int
  for +sb: Nat
  for inv: {List.length(&2, N.Rat, xt) == List.length(&2, N.Rat, yt) : Nat}
    & {Laws.fit_fits(k, x <> xt, y <> yt) == True{} : Bool}
    & {L.LinearRegression.fit.stats(True{}, PZ.lv(x <> xt, y <> yt), PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)) == Done{L.LinearRegression{True{}, N.Rat{p, qa}, N.Rat{r, sb}}} : Result<L.FitError, L.LinearRegression>}
  {Laws.sum_r(N.Rat{p, qa}, N.Rat{r, sb}, x <> xt, y <> yt) == N.Rat.zero() : N.Rat} & {Laws.sum_xr(N.Rat{p, qa}, N.Rat{r, sb}, x <> xt, y <> yt) == N.Rat.zero() : N.Rat}

def normal_eq.i(k, x, xt, y, yt, p, qa, r, sb, inv):
  match inv:
    case (len, (small, ok2)):
      normal_eq.j(k, x, xt, y, yt, p, qa, r, sb, ok2, PG.lv_pos(x <> xt, y <> yt))

law normal_eq.cc:
  for +k: Nat
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for a: N.Rat
  for b: N.Rat
  for +ok: {L.LinearRegression.fit.within(k, True{}, x <> xt, y <> yt) == Done{L.LinearRegression{True{}, a, b}} : Result<L.FitError, L.LinearRegression>}
  {Laws.sum_r(a, b, x <> xt, y <> yt) == N.Rat.zero() : N.Rat} & {Laws.sum_xr(a, b, x <> xt, y <> yt) == N.Rat.zero() : N.Rat}

def normal_eq.cc(k, x, xt, y, yt, a, b, ok):
  match a b:
    case N.Rat{+p, +qa} N.Rat{+r, +sb}:
      normal_eq.i(k, x, xt, y, yt, p, qa, r, sb, fit_inv(k, True{}, x, xt, y, yt, L.LinearRegression{True{}, N.Rat{p, qa}, N.Rat{r, sb}}, ok))

law normal_eq:
  for +k: Nat
  for xs: +List<N.Rat>
  for ys: +List<N.Rat>
  for a: N.Rat
  for b: N.Rat
  for +ok: {L.LinearRegression.fit.within(k, True{}, xs, ys) == Done{L.LinearRegression{True{}, a, b}} : Result<L.FitError, L.LinearRegression>}
  {Laws.sum_r(a, b, xs, ys) == N.Rat.zero() : N.Rat} & {Laws.sum_xr(a, b, xs, ys) == N.Rat.zero() : N.Rat}

def normal_eq(k, xs, ys, a, b, ok):
  match xs ys:
    case Nil{} _:
      ({==}, {==})
    case Con{x, xt} Nil{}:
      ({==}, {==})
    case Con{+x, +xt} Con{+y, +yt}:
      normal_eq.cc(k, x, xt, y, yt, a, b, ok)

law normal_eq_origin.f:
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +p: N.Int
  for +qa: Nat
  for +b: N.Rat
  for +lp: Nat
  for +hl: {PZ.lv(x <> xt, y <> yt) == 1n+lp : Nat}
  for +ha: {N.Int.mul(p, PG.ssxx(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt))) == N.Int.mul(PG.ssxy(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{1n+qa}) : N.Int}
  for +eb: {b == N.Rat.zero() : N.Rat}
  for +nz: {N.Int.is_eq(PG.ssxx(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{0n}) == False{} : Bool}
  {b == N.Rat.zero() : N.Rat} & {Laws.sum_xr(N.Rat{p, qa}, b, x <> xt, y <> yt) == N.Rat.zero() : N.Rat}

def normal_eq_origin.f(x, xt, y, yt, p, qa, b, lp, hl, ha, eb, nz):
  %Equal.sym(N.Rat, b, N.Rat.zero(), eb) : {_ == N.Rat.zero() : N.Rat} & {Laws.sum_xr(N.Rat{p, qa}, _, x <> xt, y <> yt) == N.Rat.zero() : N.Rat}
  ({==},
   zero_of_num(Laws.sum_xr(N.Rat{p, qa}, N.Rat.zero(), x <> xt, y <> yt),
     num_zero(Laws.sum_xr(N.Rat{p, qa}, N.Rat.zero(), x <> xt, y <> yt), N.Int.mul(N.Pos{1n+lp}, mden(N.Pos{1n+qa}, N.Pos{1n+0n}, N.Pos{1n+lp})),
       (%ne_rx_origin(p, N.Pos{1n+qa}, N.Pos{1n+lp}, PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt), ha, nz) : Laws.Denotes(Laws.sum_xr(N.Rat{p, qa}, N.Rat.zero(), x <> xt, y <> yt), _, N.Int.mul(N.Pos{1n+lp}, mden(N.Pos{1n+qa}, N.Pos{1n+0n}, N.Pos{1n+lp})))
        sumxr_den(PZ.lv(x <> xt, y <> yt), lp, hl, p, qa, N.Pos{0n}, 0n, x <> xt, y <> yt, PG.dvb_xs(x <> xt, y <> yt), PG.dvb_ys(x <> xt, y <> yt))),
       {==}),
     sumxr_canon(N.Rat{p, qa}, N.Rat.zero(), x <> xt, y <> yt)))

law normal_eq_origin.s:
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +p: N.Int
  for +qa: Nat
  for +b: N.Rat
  for +lp: Nat
  for +hl: {PZ.lv(x <> xt, y <> yt) == 1n+lp : Nat}
  for tr: Laws.Denotes(N.Rat{p, qa}, PG.ssxy(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), PG.ssxx(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt))) & {b == N.Rat.zero() : N.Rat}
    & {N.Int.is_eq(PG.ssxx(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{0n}) == False{} : Bool}
  {b == N.Rat.zero() : N.Rat} & {Laws.sum_xr(N.Rat{p, qa}, b, x <> xt, y <> yt) == N.Rat.zero() : N.Rat}

def normal_eq_origin.s(x, xt, y, yt, p, qa, b, lp, hl, tr):
  match tr:
    case (da, (eb, nz)):
      normal_eq_origin.f(x, xt, y, yt, p, qa, b, lp, hl, da, eb, nz)

law normal_eq_origin.k:
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +p: N.Int
  for +qa: Nat
  for +b: N.Rat
  for +ok2: {L.LinearRegression.fit.stats(False{}, PZ.lv(x <> xt, y <> yt), PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)) == Done{L.LinearRegression{False{}, N.Rat{p, qa}, b}} : Result<L.FitError, L.LinearRegression>}
  for +lp: Nat
  for +hl: {PZ.lv(x <> xt, y <> yt) == 1n+lp : Nat}
  {b == N.Rat.zero() : N.Rat} & {Laws.sum_xr(N.Rat{p, qa}, b, x <> xt, y <> yt) == N.Rat.zero() : N.Rat}

def normal_eq_origin.k(x, xt, y, yt, p, qa, b, ok2, lp, hl):
  normal_eq_origin.s(x, xt, y, yt, p, qa, b, lp, hl, solve_origin_inv(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt), N.Rat{p, qa}, b, ok2))

law normal_eq_origin.j:
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +p: N.Int
  for +qa: Nat
  for +b: N.Rat
  for +ok2: {L.LinearRegression.fit.stats(False{}, PZ.lv(x <> xt, y <> yt), PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)) == Done{L.LinearRegression{False{}, N.Rat{p, qa}, b}} : Result<L.FitError, L.LinearRegression>}
  for w: PD.LeW(1n, PZ.lv(x <> xt, y <> yt))
  {b == N.Rat.zero() : N.Rat} & {Laws.sum_xr(N.Rat{p, qa}, b, x <> xt, y <> yt) == N.Rat.zero() : N.Rat}

def normal_eq_origin.j(x, xt, y, yt, p, qa, b, ok2, w):
  match w:
    case (+lp, hl):
      normal_eq_origin.k(x, xt, y, yt, p, qa, b, ok2, lp, hl)

law normal_eq_origin.i:
  for +k: Nat
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +p: N.Int
  for +qa: Nat
  for +b: N.Rat
  for inv: {List.length(&2, N.Rat, xt) == List.length(&2, N.Rat, yt) : Nat}
    & {Laws.fit_fits(k, x <> xt, y <> yt) == True{} : Bool}
    & {L.LinearRegression.fit.stats(False{}, PZ.lv(x <> xt, y <> yt), PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)) == Done{L.LinearRegression{False{}, N.Rat{p, qa}, b}} : Result<L.FitError, L.LinearRegression>}
  {b == N.Rat.zero() : N.Rat} & {Laws.sum_xr(N.Rat{p, qa}, b, x <> xt, y <> yt) == N.Rat.zero() : N.Rat}

def normal_eq_origin.i(k, x, xt, y, yt, p, qa, b, inv):
  match inv:
    case (len, (small, ok2)):
      normal_eq_origin.j(x, xt, y, yt, p, qa, b, ok2, PG.lv_pos(x <> xt, y <> yt))

law normal_eq_origin.cc:
  for +k: Nat
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for a: N.Rat
  for +b: N.Rat
  for +ok: {L.LinearRegression.fit.within(k, False{}, x <> xt, y <> yt) == Done{L.LinearRegression{False{}, a, b}} : Result<L.FitError, L.LinearRegression>}
  {b == N.Rat.zero() : N.Rat} & {Laws.sum_xr(a, b, x <> xt, y <> yt) == N.Rat.zero() : N.Rat}

def normal_eq_origin.cc(k, x, xt, y, yt, a, b, ok):
  match a:
    case N.Rat{+p, +qa}:
      normal_eq_origin.i(k, x, xt, y, yt, p, qa, b, fit_inv(k, False{}, x, xt, y, yt, L.LinearRegression{False{}, N.Rat{p, qa}, b}, ok))

law normal_eq_origin:
  for +k: Nat
  for xs: +List<N.Rat>
  for ys: +List<N.Rat>
  for +a: N.Rat
  for +b: N.Rat
  for +ok: {L.LinearRegression.fit.within(k, False{}, xs, ys) == Done{L.LinearRegression{False{}, a, b}} : Result<L.FitError, L.LinearRegression>}
  {b == N.Rat.zero() : N.Rat} & {Laws.sum_xr(a, b, xs, ys) == N.Rat.zero() : N.Rat}

def normal_eq_origin(k, xs, ys, a, b, ok):
  match xs ys:
    case Nil{} Nil{}:
      Empty.absurd({b == N.Rat.zero() : N.Rat} & {Laws.sum_xr(a, b, Nil{}, Nil{}) == N.Rat.zero() : N.Rat},
        fail_ne_done(L.Empty{}, L.LinearRegression{False{}, a, b}, ok))
    case Nil{} Con{y, yt}:
      Empty.absurd({b == N.Rat.zero() : N.Rat} & {Laws.sum_xr(a, b, Nil{}, y <> yt) == N.Rat.zero() : N.Rat},
        fail_ne_done(L.LengthMismatch{}, L.LinearRegression{False{}, a, b}, ok))
    case Con{x, xt} Nil{}:
      Empty.absurd({b == N.Rat.zero() : N.Rat} & {Laws.sum_xr(a, b, x <> xt, Nil{}) == N.Rat.zero() : N.Rat},
        fail_ne_done(L.LengthMismatch{}, L.LinearRegression{False{}, a, b}, ok))
    case Con{+x, +xt} Con{+y, +yt}:
      normal_eq_origin.cc(k, x, xt, y, yt, a, b, ok)

# Least squares
# -------------
# For a second line a2 = p2 / q2, b2 = r2 / s2, with M = Lp q s, M2 = Lp q2 s2,
# U = (p q2 - p2 q) s s2 and V = (r s2 - r2 s) Lp q q2, each residual obeys
# rterm2 M == rterm M2 + Lp (U x + V), so summing the squares:
#   M² SSE2 == M2² SSE + 2 Lp M2 (U Σ x rterm + V Σ rterm) + Lp² Σ (U x + V)².

def uexp(+p: N.Int, +q: N.Int, +s: N.Int, +p2: N.Int, +q2: N.Int, +s2: N.Int) -> N.Int:
  N.Int.mul(N.Int.sub(N.Int.mul(p, q2), N.Int.mul(p2, q)), N.Int.mul(s, s2))

def vexp(+r: N.Int, +q: N.Int, +s: N.Int, +r2: N.Int, +q2: N.Int, +s2: N.Int, +lp: N.Int) -> N.Int:
  N.Int.mul(N.Int.sub(N.Int.mul(r, s2), N.Int.mul(r2, s)), N.Int.mul(lp, N.Int.mul(q, q2)))

# Σ (u x + v), Σ x (u x + v) and Σ (u x + v)², from the sums
def w1(+u: N.Int, +v: N.Int, +st: L.Stats) -> N.Int:
  N.Int.add(N.Int.mul(u, PG.ssx(st)), N.Int.mul(v, PG.sn(st)))

def wx(+u: N.Int, +v: N.Int, +st: L.Stats) -> N.Int:
  N.Int.add(N.Int.mul(u, PG.ssxx(st)), N.Int.mul(v, PG.ssx(st)))

def w2(+u: N.Int, +v: N.Int, +st: L.Stats) -> N.Int:
  N.Int.add(N.Int.add(N.Int.mul(N.Int.mul(u, u), PG.ssxx(st)), N.Int.mul(N.Int.mul(N.Int.mul(N.Pos{2n}, u), v), PG.ssx(st))),
    N.Int.mul(N.Int.mul(v, v), PG.sn(st)))

def wt(+u: N.Int, +v: N.Int, +x: N.Int) -> N.Int:
  N.Int.add(N.Int.mul(u, x), v)

law w1_step:
  for +u: N.Int
  for +v: N.Int
  for +x: N.Int
  for +y: N.Int
  for st: L.Stats
  {w1(u, v, L.Stats.add(PG.pt(x, y), st)) == N.Int.add(wt(u, v, x), w1(u, v, st)) : N.Int}

def w1_step(u, v, x, y, st):
  match st:
    case L.Stats{+n, +sx, sy, sxy, sxx}:
      PI.IRing.eq(PI.IAdd{PI.IMul{PI.IVar{0n}, PI.IAdd{PI.IVar{2n}, PI.IVar{4n}}}, PI.IMul{PI.IVar{1n}, PI.IAdd{PI.IConst{N.Pos{1n}}, PI.IVar{3n}}}}, PI.IAdd{PI.IAdd{PI.IMul{PI.IVar{0n}, PI.IVar{2n}}, PI.IVar{1n}}, PI.IAdd{PI.IMul{PI.IVar{0n}, PI.IVar{4n}}, PI.IMul{PI.IVar{1n}, PI.IVar{3n}}}}, [u, v, x, n, sx], {==})

law wx_step:
  for +u: N.Int
  for +v: N.Int
  for +x: N.Int
  for +y: N.Int
  for st: L.Stats
  {wx(u, v, L.Stats.add(PG.pt(x, y), st)) == N.Int.add(N.Int.mul(x, wt(u, v, x)), wx(u, v, st)) : N.Int}

def wx_step(u, v, x, y, st):
  match st:
    case L.Stats{n, +sx, sy, sxy, +sxx}:
      PI.IRing.eq(PI.IAdd{PI.IMul{PI.IVar{0n}, PI.IAdd{PI.IMul{PI.IVar{2n}, PI.IVar{2n}}, PI.IVar{4n}}}, PI.IMul{PI.IVar{1n}, PI.IAdd{PI.IVar{2n}, PI.IVar{3n}}}}, PI.IAdd{PI.IMul{PI.IVar{2n}, PI.IAdd{PI.IMul{PI.IVar{0n}, PI.IVar{2n}}, PI.IVar{1n}}}, PI.IAdd{PI.IMul{PI.IVar{0n}, PI.IVar{4n}}, PI.IMul{PI.IVar{1n}, PI.IVar{3n}}}}, [u, v, x, sx, sxx], {==})

law w2_step:
  for +u: N.Int
  for +v: N.Int
  for +x: N.Int
  for +y: N.Int
  for st: L.Stats
  {w2(u, v, L.Stats.add(PG.pt(x, y), st)) == N.Int.add(PG.sq(wt(u, v, x)), w2(u, v, st)) : N.Int}

def w2_step(u, v, x, y, st):
  match st:
    case L.Stats{+n, +sx, sy, sxy, +sxx}:
      PI.IRing.eq(PI.IAdd{PI.IAdd{PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{0n}}, PI.IAdd{PI.IMul{PI.IVar{2n}, PI.IVar{2n}}, PI.IVar{5n}}}, PI.IMul{PI.IMul{PI.IMul{PI.IConst{N.Pos{2n}}, PI.IVar{0n}}, PI.IVar{1n}}, PI.IAdd{PI.IVar{2n}, PI.IVar{4n}}}}, PI.IMul{PI.IMul{PI.IVar{1n}, PI.IVar{1n}}, PI.IAdd{PI.IConst{N.Pos{1n}}, PI.IVar{3n}}}}, PI.IAdd{PI.IMul{PI.IAdd{PI.IMul{PI.IVar{0n}, PI.IVar{2n}}, PI.IVar{1n}}, PI.IAdd{PI.IMul{PI.IVar{0n}, PI.IVar{2n}}, PI.IVar{1n}}}, PI.IAdd{PI.IAdd{PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{0n}}, PI.IVar{5n}}, PI.IMul{PI.IMul{PI.IMul{PI.IConst{N.Pos{2n}}, PI.IVar{0n}}, PI.IVar{1n}}, PI.IVar{4n}}}, PI.IMul{PI.IMul{PI.IVar{1n}, PI.IVar{1n}}, PI.IVar{3n}}}}, [u, v, x, n, sx, sxx], {==})

law w1_zero:
  for +u: N.Int
  for +v: N.Int
  {w1(u, v, L.Stats.zero()) == N.Pos{0n} : N.Int}

def w1_zero(u, v):
  PI.IRing.eq(PI.IAdd{PI.IMul{PI.IVar{0n}, PI.IConst{N.Pos{0n}}}, PI.IMul{PI.IVar{1n}, PI.IConst{N.Pos{0n}}}}, PI.IConst{N.Pos{0n}}, [u, v], {==})

law wx_zero:
  for +u: N.Int
  for +v: N.Int
  {wx(u, v, L.Stats.zero()) == N.Pos{0n} : N.Int}

def wx_zero(u, v):
  PI.IRing.eq(PI.IAdd{PI.IMul{PI.IVar{0n}, PI.IConst{N.Pos{0n}}}, PI.IMul{PI.IVar{1n}, PI.IConst{N.Pos{0n}}}}, PI.IConst{N.Pos{0n}}, [u, v], {==})

law w2_zero:
  for +u: N.Int
  for +v: N.Int
  {w2(u, v, L.Stats.zero()) == N.Pos{0n} : N.Int}

def w2_zero(u, v):
  PI.IRing.eq(PI.IAdd{PI.IAdd{PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{0n}}, PI.IConst{N.Pos{0n}}}, PI.IMul{PI.IMul{PI.IMul{PI.IConst{N.Pos{2n}}, PI.IVar{0n}}, PI.IVar{1n}}, PI.IConst{N.Pos{0n}}}}, PI.IMul{PI.IMul{PI.IVar{1n}, PI.IVar{1n}}, PI.IConst{N.Pos{0n}}}}, PI.IConst{N.Pos{0n}}, [u, v], {==})

law w2_nonneg:
  for +u: N.Int
  for +v: N.Int
  for +l: Nat
  for ps: +List<L.Point>
  PR.Int.isp(w2(u, v, L.Stats.seq(l, ps)))

def w2_nonneg(u, v, l, ps):
  match ps:
    case Nil{}:
      %Equal.sym(N.Int, w2(u, v, L.Stats.zero()), N.Pos{0n}, w2_zero(u, v)) : PR.Int.isp(_)
      Unit{}
    case Con{L.Pt{+x, +y}, +t}:
      %Equal.sym(N.Int, w2(u, v, L.Stats.add(PG.pt(L.Stats.scale(l, x), L.Stats.scale(l, y)), L.Stats.seq(l, t))),
          N.Int.add(PG.sq(wt(u, v, L.Stats.scale(l, x))), w2(u, v, L.Stats.seq(l, t))),
          w2_step(u, v, L.Stats.scale(l, x), L.Stats.scale(l, y), L.Stats.seq(l, t)))
        : PR.Int.isp(_)
      PG.isp_add(PG.sq(wt(u, v, L.Stats.scale(l, x))), w2(u, v, L.Stats.seq(l, t)),
        PG.isp_sq(wt(u, v, L.Stats.scale(l, x))), w2_nonneg(u, v, l, t))

# Σ (u x + v)² == 0 makes w1 == 0
law w1_of_w2:
  for +u: N.Int
  for +v: N.Int
  for +l: Nat
  for ps: +List<L.Point>
  for +h: {w2(u, v, L.Stats.seq(l, ps)) == N.Pos{0n} : N.Int}
  {w1(u, v, L.Stats.seq(l, ps)) == N.Pos{0n} : N.Int}

def w1_of_w2(u, v, l, ps, h):
  match ps:
    case Nil{}:
      w1_zero(u, v)
    case Con{L.Pt{+x, +y}, +t}:
      %Equal.sym(N.Int, w1(u, v, L.Stats.add(PG.pt(L.Stats.scale(l, x), L.Stats.scale(l, y)), L.Stats.seq(l, t))), N.Int.add(wt(u, v, L.Stats.scale(l, x)), w1(u, v, L.Stats.seq(l, t))),
          w1_step(u, v, L.Stats.scale(l, x), L.Stats.scale(l, y), L.Stats.seq(l, t)))
        : {_ == N.Pos{0n} : N.Int}
      %Equal.sym(N.Int, wt(u, v, L.Stats.scale(l, x)), N.Pos{0n},
          PG.sq_zero(wt(u, v, L.Stats.scale(l, x)),
            PG.add_zero_l(PG.sq(wt(u, v, L.Stats.scale(l, x))), w2(u, v, L.Stats.seq(l, t)), PG.isp_sq(wt(u, v, L.Stats.scale(l, x))), w2_nonneg(u, v, l, t),
              Equal.trans(N.Int, N.Int.add(PG.sq(wt(u, v, L.Stats.scale(l, x))), w2(u, v, L.Stats.seq(l, t))),
                w2(u, v, L.Stats.add(PG.pt(L.Stats.scale(l, x), L.Stats.scale(l, y)), L.Stats.seq(l, t))), N.Pos{0n},
                Equal.sym(N.Int, w2(u, v, L.Stats.add(PG.pt(L.Stats.scale(l, x), L.Stats.scale(l, y)), L.Stats.seq(l, t))), N.Int.add(PG.sq(wt(u, v, L.Stats.scale(l, x))), w2(u, v, L.Stats.seq(l, t))),
                  w2_step(u, v, L.Stats.scale(l, x), L.Stats.scale(l, y), L.Stats.seq(l, t))),
                h))))
        : {N.Int.add(_, w1(u, v, L.Stats.seq(l, t))) == N.Pos{0n} : N.Int}
      %Equal.sym(N.Int, w1(u, v, L.Stats.seq(l, t)), N.Pos{0n},
          w1_of_w2(u, v, l, t,
            PG.add_zero_r(PG.sq(wt(u, v, L.Stats.scale(l, x))), w2(u, v, L.Stats.seq(l, t)), PG.isp_sq(wt(u, v, L.Stats.scale(l, x))), w2_nonneg(u, v, l, t),
              Equal.trans(N.Int, N.Int.add(PG.sq(wt(u, v, L.Stats.scale(l, x))), w2(u, v, L.Stats.seq(l, t))),
                w2(u, v, L.Stats.add(PG.pt(L.Stats.scale(l, x), L.Stats.scale(l, y)), L.Stats.seq(l, t))), N.Pos{0n},
                Equal.sym(N.Int, w2(u, v, L.Stats.add(PG.pt(L.Stats.scale(l, x), L.Stats.scale(l, y)), L.Stats.seq(l, t))), N.Int.add(PG.sq(wt(u, v, L.Stats.scale(l, x))), w2(u, v, L.Stats.seq(l, t))),
                  w2_step(u, v, L.Stats.scale(l, x), L.Stats.scale(l, y), L.Stats.seq(l, t))),
                h))))
        : {N.Int.add(N.Pos{0n}, _) == N.Pos{0n} : N.Int}
      PI.IRing.eq(PI.IAdd{PI.IConst{N.Pos{0n}}, PI.IConst{N.Pos{0n}}}, PI.IConst{N.Pos{0n}}, [L.Stats.scale(l, x)], {==})

# Σ (u x + v)² == 0 makes wx == 0
law wx_of_w2:
  for +u: N.Int
  for +v: N.Int
  for +l: Nat
  for ps: +List<L.Point>
  for +h: {w2(u, v, L.Stats.seq(l, ps)) == N.Pos{0n} : N.Int}
  {wx(u, v, L.Stats.seq(l, ps)) == N.Pos{0n} : N.Int}

def wx_of_w2(u, v, l, ps, h):
  match ps:
    case Nil{}:
      wx_zero(u, v)
    case Con{L.Pt{+x, +y}, +t}:
      %Equal.sym(N.Int, wx(u, v, L.Stats.add(PG.pt(L.Stats.scale(l, x), L.Stats.scale(l, y)), L.Stats.seq(l, t))), N.Int.add(N.Int.mul(L.Stats.scale(l, x), wt(u, v, L.Stats.scale(l, x))), wx(u, v, L.Stats.seq(l, t))),
          wx_step(u, v, L.Stats.scale(l, x), L.Stats.scale(l, y), L.Stats.seq(l, t)))
        : {_ == N.Pos{0n} : N.Int}
      %Equal.sym(N.Int, wt(u, v, L.Stats.scale(l, x)), N.Pos{0n},
          PG.sq_zero(wt(u, v, L.Stats.scale(l, x)),
            PG.add_zero_l(PG.sq(wt(u, v, L.Stats.scale(l, x))), w2(u, v, L.Stats.seq(l, t)), PG.isp_sq(wt(u, v, L.Stats.scale(l, x))), w2_nonneg(u, v, l, t),
              Equal.trans(N.Int, N.Int.add(PG.sq(wt(u, v, L.Stats.scale(l, x))), w2(u, v, L.Stats.seq(l, t))),
                w2(u, v, L.Stats.add(PG.pt(L.Stats.scale(l, x), L.Stats.scale(l, y)), L.Stats.seq(l, t))), N.Pos{0n},
                Equal.sym(N.Int, w2(u, v, L.Stats.add(PG.pt(L.Stats.scale(l, x), L.Stats.scale(l, y)), L.Stats.seq(l, t))), N.Int.add(PG.sq(wt(u, v, L.Stats.scale(l, x))), w2(u, v, L.Stats.seq(l, t))),
                  w2_step(u, v, L.Stats.scale(l, x), L.Stats.scale(l, y), L.Stats.seq(l, t))),
                h))))
        : {N.Int.add(N.Int.mul(L.Stats.scale(l, x), _), wx(u, v, L.Stats.seq(l, t))) == N.Pos{0n} : N.Int}
      %Equal.sym(N.Int, wx(u, v, L.Stats.seq(l, t)), N.Pos{0n},
          wx_of_w2(u, v, l, t,
            PG.add_zero_r(PG.sq(wt(u, v, L.Stats.scale(l, x))), w2(u, v, L.Stats.seq(l, t)), PG.isp_sq(wt(u, v, L.Stats.scale(l, x))), w2_nonneg(u, v, l, t),
              Equal.trans(N.Int, N.Int.add(PG.sq(wt(u, v, L.Stats.scale(l, x))), w2(u, v, L.Stats.seq(l, t))),
                w2(u, v, L.Stats.add(PG.pt(L.Stats.scale(l, x), L.Stats.scale(l, y)), L.Stats.seq(l, t))), N.Pos{0n},
                Equal.sym(N.Int, w2(u, v, L.Stats.add(PG.pt(L.Stats.scale(l, x), L.Stats.scale(l, y)), L.Stats.seq(l, t))), N.Int.add(PG.sq(wt(u, v, L.Stats.scale(l, x))), w2(u, v, L.Stats.seq(l, t))),
                  w2_step(u, v, L.Stats.scale(l, x), L.Stats.scale(l, y), L.Stats.seq(l, t))),
                h))))
        : {N.Int.add(N.Int.mul(L.Stats.scale(l, x), N.Pos{0n}), _) == N.Pos{0n} : N.Int}
      PI.IRing.eq(PI.IAdd{PI.IMul{PI.IVar{0n}, PI.IConst{N.Pos{0n}}}, PI.IConst{N.Pos{0n}}}, PI.IConst{N.Pos{0n}}, [L.Stats.scale(l, x)], {==})

# one residual: rterm2 M == rterm M2 + Lp (U x + V)
law lin:
  for +lp: N.Int
  for +p: N.Int
  for +q: N.Int
  for +r: N.Int
  for +s: N.Int
  for +p2: N.Int
  for +q2: N.Int
  for +r2: N.Int
  for +s2: N.Int
  for +x: N.Int
  for +y: N.Int
  {N.Int.mul(rterm(p2, q2, r2, s2, lp, x, y), mden(q, s, lp)) == N.Int.add(N.Int.mul(rterm(p, q, r, s, lp, x, y), mden(q2, s2, lp)), N.Int.mul(lp, wt(uexp(p, q, s, p2, q2, s2), vexp(r, q, s, r2, q2, s2, lp), x))) : N.Int}

def lin(lp, p, q, r, s, p2, q2, r2, s2, x, y):
  PI.IRing.eq(PI.IMul{PI.IAdd{PI.IAdd{PI.IMul{PI.IMul{PI.IVar{1n}, PI.IVar{7n}}, PI.IVar{9n}}, PI.INeg{PI.IMul{PI.IMul{PI.IVar{6n}, PI.IVar{0n}}, PI.IVar{9n}}}}, PI.INeg{PI.IMul{PI.IMul{PI.IVar{8n}, PI.IVar{7n}}, PI.IVar{10n}}}}, PI.IMul{PI.IMul{PI.IVar{10n}, PI.IVar{3n}}, PI.IVar{5n}}}, PI.IAdd{PI.IMul{PI.IAdd{PI.IAdd{PI.IMul{PI.IMul{PI.IVar{1n}, PI.IVar{3n}}, PI.IVar{5n}}, PI.INeg{PI.IMul{PI.IMul{PI.IVar{2n}, PI.IVar{0n}}, PI.IVar{5n}}}}, PI.INeg{PI.IMul{PI.IMul{PI.IVar{4n}, PI.IVar{3n}}, PI.IVar{10n}}}}, PI.IMul{PI.IMul{PI.IVar{10n}, PI.IVar{7n}}, PI.IVar{9n}}}, PI.IMul{PI.IVar{10n}, PI.IAdd{PI.IMul{PI.IMul{PI.IAdd{PI.IMul{PI.IVar{2n}, PI.IVar{7n}}, PI.INeg{PI.IMul{PI.IVar{6n}, PI.IVar{3n}}}}, PI.IMul{PI.IVar{5n}, PI.IVar{9n}}}, PI.IVar{0n}}, PI.IMul{PI.IAdd{PI.IMul{PI.IVar{4n}, PI.IVar{9n}}, PI.INeg{PI.IMul{PI.IVar{8n}, PI.IVar{5n}}}}, PI.IMul{PI.IVar{10n}, PI.IMul{PI.IVar{3n}, PI.IVar{7n}}}}}}}, [x, y, p, q, r, s, p2, q2, r2, s2, lp], {==})

law key:
  for +lp: N.Int
  for +p: N.Int
  for +q: N.Int
  for +r: N.Int
  for +s: N.Int
  for +p2: N.Int
  for +q2: N.Int
  for +r2: N.Int
  for +s2: N.Int
  for +l: Nat
  for xs: +List<N.Rat>
  for ys: +List<N.Rat>
  {N.Int.mul(N.Int.mul(mden(q, s, lp), mden(q, s, lp)), sumsq(p2, q2, r2, s2, lp, l, xs, ys)) == N.Int.add(N.Int.add(N.Int.mul(N.Int.mul(mden(q2, s2, lp), mden(q2, s2, lp)), sumsq(p, q, r, s, lp, l, xs, ys)), N.Int.mul(N.Int.mul(N.Int.mul(N.Pos{2n}, lp), mden(q2, s2, lp)), N.Int.add(N.Int.mul(uexp(p, q, s, p2, q2, s2), rxexp(p, q, r, s, lp, PG.rest(l, xs, ys))), N.Int.mul(vexp(r, q, s, r2, q2, s2, lp), rexp(p, q, r, s, lp, PG.rest(l, xs, ys)))))), N.Int.mul(N.Int.mul(lp, lp), w2(uexp(p, q, s, p2, q2, s2), vexp(r, q, s, r2, q2, s2, lp), PG.rest(l, xs, ys)))) : N.Int}

def key(lp, p, q, r, s, p2, q2, r2, s2, l, xs, ys):
  match xs ys:
    case Nil{} _:
      %Equal.sym(N.Int, rxexp(p, q, r, s, lp, L.Stats.zero()), N.Pos{0n}, rxexp_zero(p, q, r, s, lp))
        : {N.Int.mul(N.Int.mul(mden(q, s, lp), mden(q, s, lp)), N.Pos{0n}) == N.Int.add(N.Int.add(N.Int.mul(N.Int.mul(mden(q2, s2, lp), mden(q2, s2, lp)), N.Pos{0n}), N.Int.mul(N.Int.mul(N.Int.mul(N.Pos{2n}, lp), mden(q2, s2, lp)), N.Int.add(N.Int.mul(uexp(p, q, s, p2, q2, s2), _), N.Int.mul(vexp(r, q, s, r2, q2, s2, lp), rexp(p, q, r, s, lp, L.Stats.zero()))))), N.Int.mul(N.Int.mul(lp, lp), w2(uexp(p, q, s, p2, q2, s2), vexp(r, q, s, r2, q2, s2, lp), L.Stats.zero()))) : N.Int}
      %Equal.sym(N.Int, rexp(p, q, r, s, lp, L.Stats.zero()), N.Pos{0n}, rexp_zero(p, q, r, s, lp))
        : {N.Int.mul(N.Int.mul(mden(q, s, lp), mden(q, s, lp)), N.Pos{0n}) == N.Int.add(N.Int.add(N.Int.mul(N.Int.mul(mden(q2, s2, lp), mden(q2, s2, lp)), N.Pos{0n}), N.Int.mul(N.Int.mul(N.Int.mul(N.Pos{2n}, lp), mden(q2, s2, lp)), N.Int.add(N.Int.mul(uexp(p, q, s, p2, q2, s2), N.Pos{0n}), N.Int.mul(vexp(r, q, s, r2, q2, s2, lp), _)))), N.Int.mul(N.Int.mul(lp, lp), w2(uexp(p, q, s, p2, q2, s2), vexp(r, q, s, r2, q2, s2, lp), L.Stats.zero()))) : N.Int}
      %Equal.sym(N.Int, w2(uexp(p, q, s, p2, q2, s2), vexp(r, q, s, r2, q2, s2, lp), L.Stats.zero()), N.Pos{0n}, w2_zero(uexp(p, q, s, p2, q2, s2), vexp(r, q, s, r2, q2, s2, lp)))
        : {N.Int.mul(N.Int.mul(mden(q, s, lp), mden(q, s, lp)), N.Pos{0n}) == N.Int.add(N.Int.add(N.Int.mul(N.Int.mul(mden(q2, s2, lp), mden(q2, s2, lp)), N.Pos{0n}), N.Int.mul(N.Int.mul(N.Int.mul(N.Pos{2n}, lp), mden(q2, s2, lp)), N.Int.add(N.Int.mul(uexp(p, q, s, p2, q2, s2), N.Pos{0n}), N.Int.mul(vexp(r, q, s, r2, q2, s2, lp), N.Pos{0n})))), N.Int.mul(N.Int.mul(lp, lp), _)) : N.Int}
      PI.IRing.eq(PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{0n}}, PI.IConst{N.Pos{0n}}}, PI.IAdd{PI.IAdd{PI.IMul{PI.IMul{PI.IVar{1n}, PI.IVar{1n}}, PI.IConst{N.Pos{0n}}}, PI.IMul{PI.IVar{2n}, PI.IAdd{PI.IMul{PI.IVar{3n}, PI.IConst{N.Pos{0n}}}, PI.IMul{PI.IVar{4n}, PI.IConst{N.Pos{0n}}}}}}, PI.IMul{PI.IVar{5n}, PI.IConst{N.Pos{0n}}}}, [mden(q, s, lp), mden(q2, s2, lp), N.Int.mul(N.Int.mul(N.Pos{2n}, lp), mden(q2, s2, lp)), uexp(p, q, s, p2, q2, s2), vexp(r, q, s, r2, q2, s2, lp), N.Int.mul(lp, lp)], {==})
    case Con{x, xt} Nil{}:
      %Equal.sym(N.Int, rxexp(p, q, r, s, lp, L.Stats.zero()), N.Pos{0n}, rxexp_zero(p, q, r, s, lp))
        : {N.Int.mul(N.Int.mul(mden(q, s, lp), mden(q, s, lp)), N.Pos{0n}) == N.Int.add(N.Int.add(N.Int.mul(N.Int.mul(mden(q2, s2, lp), mden(q2, s2, lp)), N.Pos{0n}), N.Int.mul(N.Int.mul(N.Int.mul(N.Pos{2n}, lp), mden(q2, s2, lp)), N.Int.add(N.Int.mul(uexp(p, q, s, p2, q2, s2), _), N.Int.mul(vexp(r, q, s, r2, q2, s2, lp), rexp(p, q, r, s, lp, L.Stats.zero()))))), N.Int.mul(N.Int.mul(lp, lp), w2(uexp(p, q, s, p2, q2, s2), vexp(r, q, s, r2, q2, s2, lp), L.Stats.zero()))) : N.Int}
      %Equal.sym(N.Int, rexp(p, q, r, s, lp, L.Stats.zero()), N.Pos{0n}, rexp_zero(p, q, r, s, lp))
        : {N.Int.mul(N.Int.mul(mden(q, s, lp), mden(q, s, lp)), N.Pos{0n}) == N.Int.add(N.Int.add(N.Int.mul(N.Int.mul(mden(q2, s2, lp), mden(q2, s2, lp)), N.Pos{0n}), N.Int.mul(N.Int.mul(N.Int.mul(N.Pos{2n}, lp), mden(q2, s2, lp)), N.Int.add(N.Int.mul(uexp(p, q, s, p2, q2, s2), N.Pos{0n}), N.Int.mul(vexp(r, q, s, r2, q2, s2, lp), _)))), N.Int.mul(N.Int.mul(lp, lp), w2(uexp(p, q, s, p2, q2, s2), vexp(r, q, s, r2, q2, s2, lp), L.Stats.zero()))) : N.Int}
      %Equal.sym(N.Int, w2(uexp(p, q, s, p2, q2, s2), vexp(r, q, s, r2, q2, s2, lp), L.Stats.zero()), N.Pos{0n}, w2_zero(uexp(p, q, s, p2, q2, s2), vexp(r, q, s, r2, q2, s2, lp)))
        : {N.Int.mul(N.Int.mul(mden(q, s, lp), mden(q, s, lp)), N.Pos{0n}) == N.Int.add(N.Int.add(N.Int.mul(N.Int.mul(mden(q2, s2, lp), mden(q2, s2, lp)), N.Pos{0n}), N.Int.mul(N.Int.mul(N.Int.mul(N.Pos{2n}, lp), mden(q2, s2, lp)), N.Int.add(N.Int.mul(uexp(p, q, s, p2, q2, s2), N.Pos{0n}), N.Int.mul(vexp(r, q, s, r2, q2, s2, lp), N.Pos{0n})))), N.Int.mul(N.Int.mul(lp, lp), _)) : N.Int}
      PI.IRing.eq(PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{0n}}, PI.IConst{N.Pos{0n}}}, PI.IAdd{PI.IAdd{PI.IMul{PI.IMul{PI.IVar{1n}, PI.IVar{1n}}, PI.IConst{N.Pos{0n}}}, PI.IMul{PI.IVar{2n}, PI.IAdd{PI.IMul{PI.IVar{3n}, PI.IConst{N.Pos{0n}}}, PI.IMul{PI.IVar{4n}, PI.IConst{N.Pos{0n}}}}}}, PI.IMul{PI.IVar{5n}, PI.IConst{N.Pos{0n}}}}, [mden(q, s, lp), mden(q2, s2, lp), N.Int.mul(N.Int.mul(N.Pos{2n}, lp), mden(q2, s2, lp)), uexp(p, q, s, p2, q2, s2), vexp(r, q, s, r2, q2, s2, lp), N.Int.mul(lp, lp)], {==})
    case Con{+x, +xt} Con{+y, +yt}:
      %Equal.sym(N.Int, rxexp(p, q, r, s, lp, L.Stats.add(PG.pt(L.Stats.scale(l, x), L.Stats.scale(l, y)), PG.rest(l, xt, yt))), N.Int.add(N.Int.mul(L.Stats.scale(l, x), rterm(p, q, r, s, lp, L.Stats.scale(l, x), L.Stats.scale(l, y))), rxexp(p, q, r, s, lp, PG.rest(l, xt, yt))), rxexp_step(p, q, r, s, lp, L.Stats.scale(l, x), L.Stats.scale(l, y), PG.rest(l, xt, yt)))
        : {N.Int.mul(N.Int.mul(mden(q, s, lp), mden(q, s, lp)), N.Int.add(PG.sq(rterm(p2, q2, r2, s2, lp, L.Stats.scale(l, x), L.Stats.scale(l, y))), sumsq(p2, q2, r2, s2, lp, l, xt, yt))) == N.Int.add(N.Int.add(N.Int.mul(N.Int.mul(mden(q2, s2, lp), mden(q2, s2, lp)), N.Int.add(PG.sq(rterm(p, q, r, s, lp, L.Stats.scale(l, x), L.Stats.scale(l, y))), sumsq(p, q, r, s, lp, l, xt, yt))), N.Int.mul(N.Int.mul(N.Int.mul(N.Pos{2n}, lp), mden(q2, s2, lp)), N.Int.add(N.Int.mul(uexp(p, q, s, p2, q2, s2), _), N.Int.mul(vexp(r, q, s, r2, q2, s2, lp), rexp(p, q, r, s, lp, L.Stats.add(PG.pt(L.Stats.scale(l, x), L.Stats.scale(l, y)), PG.rest(l, xt, yt))))))), N.Int.mul(N.Int.mul(lp, lp), w2(uexp(p, q, s, p2, q2, s2), vexp(r, q, s, r2, q2, s2, lp), L.Stats.add(PG.pt(L.Stats.scale(l, x), L.Stats.scale(l, y)), PG.rest(l, xt, yt))))) : N.Int}
      %Equal.sym(N.Int, rexp(p, q, r, s, lp, L.Stats.add(PG.pt(L.Stats.scale(l, x), L.Stats.scale(l, y)), PG.rest(l, xt, yt))), N.Int.add(rterm(p, q, r, s, lp, L.Stats.scale(l, x), L.Stats.scale(l, y)), rexp(p, q, r, s, lp, PG.rest(l, xt, yt))), rexp_step(p, q, r, s, lp, L.Stats.scale(l, x), L.Stats.scale(l, y), PG.rest(l, xt, yt)))
        : {N.Int.mul(N.Int.mul(mden(q, s, lp), mden(q, s, lp)), N.Int.add(PG.sq(rterm(p2, q2, r2, s2, lp, L.Stats.scale(l, x), L.Stats.scale(l, y))), sumsq(p2, q2, r2, s2, lp, l, xt, yt))) == N.Int.add(N.Int.add(N.Int.mul(N.Int.mul(mden(q2, s2, lp), mden(q2, s2, lp)), N.Int.add(PG.sq(rterm(p, q, r, s, lp, L.Stats.scale(l, x), L.Stats.scale(l, y))), sumsq(p, q, r, s, lp, l, xt, yt))), N.Int.mul(N.Int.mul(N.Int.mul(N.Pos{2n}, lp), mden(q2, s2, lp)), N.Int.add(N.Int.mul(uexp(p, q, s, p2, q2, s2), N.Int.add(N.Int.mul(L.Stats.scale(l, x), rterm(p, q, r, s, lp, L.Stats.scale(l, x), L.Stats.scale(l, y))), rxexp(p, q, r, s, lp, PG.rest(l, xt, yt)))), N.Int.mul(vexp(r, q, s, r2, q2, s2, lp), _)))), N.Int.mul(N.Int.mul(lp, lp), w2(uexp(p, q, s, p2, q2, s2), vexp(r, q, s, r2, q2, s2, lp), L.Stats.add(PG.pt(L.Stats.scale(l, x), L.Stats.scale(l, y)), PG.rest(l, xt, yt))))) : N.Int}
      %Equal.sym(N.Int, w2(uexp(p, q, s, p2, q2, s2), vexp(r, q, s, r2, q2, s2, lp), L.Stats.add(PG.pt(L.Stats.scale(l, x), L.Stats.scale(l, y)), PG.rest(l, xt, yt))), N.Int.add(PG.sq(wt(uexp(p, q, s, p2, q2, s2), vexp(r, q, s, r2, q2, s2, lp), L.Stats.scale(l, x))), w2(uexp(p, q, s, p2, q2, s2), vexp(r, q, s, r2, q2, s2, lp), PG.rest(l, xt, yt))), w2_step(uexp(p, q, s, p2, q2, s2), vexp(r, q, s, r2, q2, s2, lp), L.Stats.scale(l, x), L.Stats.scale(l, y), PG.rest(l, xt, yt)))
        : {N.Int.mul(N.Int.mul(mden(q, s, lp), mden(q, s, lp)), N.Int.add(PG.sq(rterm(p2, q2, r2, s2, lp, L.Stats.scale(l, x), L.Stats.scale(l, y))), sumsq(p2, q2, r2, s2, lp, l, xt, yt))) == N.Int.add(N.Int.add(N.Int.mul(N.Int.mul(mden(q2, s2, lp), mden(q2, s2, lp)), N.Int.add(PG.sq(rterm(p, q, r, s, lp, L.Stats.scale(l, x), L.Stats.scale(l, y))), sumsq(p, q, r, s, lp, l, xt, yt))), N.Int.mul(N.Int.mul(N.Int.mul(N.Pos{2n}, lp), mden(q2, s2, lp)), N.Int.add(N.Int.mul(uexp(p, q, s, p2, q2, s2), N.Int.add(N.Int.mul(L.Stats.scale(l, x), rterm(p, q, r, s, lp, L.Stats.scale(l, x), L.Stats.scale(l, y))), rxexp(p, q, r, s, lp, PG.rest(l, xt, yt)))), N.Int.mul(vexp(r, q, s, r2, q2, s2, lp), N.Int.add(rterm(p, q, r, s, lp, L.Stats.scale(l, x), L.Stats.scale(l, y)), rexp(p, q, r, s, lp, PG.rest(l, xt, yt))))))), N.Int.mul(N.Int.mul(lp, lp), _)) : N.Int}
      Equal.trans(N.Int, N.Int.mul(N.Int.mul(mden(q, s, lp), mden(q, s, lp)), N.Int.add(PG.sq(rterm(p2, q2, r2, s2, lp, L.Stats.scale(l, x), L.Stats.scale(l, y))), sumsq(p2, q2, r2, s2, lp, l, xt, yt))),
        N.Int.add(N.Int.mul(N.Int.mul(rterm(p2, q2, r2, s2, lp, L.Stats.scale(l, x), L.Stats.scale(l, y)), mden(q, s, lp)), N.Int.mul(rterm(p2, q2, r2, s2, lp, L.Stats.scale(l, x), L.Stats.scale(l, y)), mden(q, s, lp))), N.Int.mul(N.Int.mul(mden(q, s, lp), mden(q, s, lp)), sumsq(p2, q2, r2, s2, lp, l, xt, yt))), N.Int.add(N.Int.add(N.Int.mul(N.Int.mul(mden(q2, s2, lp), mden(q2, s2, lp)), N.Int.add(PG.sq(rterm(p, q, r, s, lp, L.Stats.scale(l, x), L.Stats.scale(l, y))), sumsq(p, q, r, s, lp, l, xt, yt))), N.Int.mul(N.Int.mul(N.Int.mul(N.Pos{2n}, lp), mden(q2, s2, lp)), N.Int.add(N.Int.mul(uexp(p, q, s, p2, q2, s2), N.Int.add(N.Int.mul(L.Stats.scale(l, x), rterm(p, q, r, s, lp, L.Stats.scale(l, x), L.Stats.scale(l, y))), rxexp(p, q, r, s, lp, PG.rest(l, xt, yt)))), N.Int.mul(vexp(r, q, s, r2, q2, s2, lp), N.Int.add(rterm(p, q, r, s, lp, L.Stats.scale(l, x), L.Stats.scale(l, y)), rexp(p, q, r, s, lp, PG.rest(l, xt, yt))))))), N.Int.mul(N.Int.mul(lp, lp), N.Int.add(PG.sq(wt(uexp(p, q, s, p2, q2, s2), vexp(r, q, s, r2, q2, s2, lp), L.Stats.scale(l, x))), w2(uexp(p, q, s, p2, q2, s2), vexp(r, q, s, r2, q2, s2, lp), PG.rest(l, xt, yt))))),
        PI.IRing.eq(PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{0n}}, PI.IAdd{PI.IMul{PI.IVar{1n}, PI.IVar{1n}}, PI.IVar{2n}}}, PI.IAdd{PI.IMul{PI.IMul{PI.IVar{1n}, PI.IVar{0n}}, PI.IMul{PI.IVar{1n}, PI.IVar{0n}}}, PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{0n}}, PI.IVar{2n}}}, [mden(q, s, lp), rterm(p2, q2, r2, s2, lp, L.Stats.scale(l, x), L.Stats.scale(l, y)), sumsq(p2, q2, r2, s2, lp, l, xt, yt)], {==}),
        (%Equal.sym(N.Int, N.Int.mul(N.Int.mul(mden(q, s, lp), mden(q, s, lp)), sumsq(p2, q2, r2, s2, lp, l, xt, yt)), N.Int.add(N.Int.add(N.Int.mul(N.Int.mul(mden(q2, s2, lp), mden(q2, s2, lp)), sumsq(p, q, r, s, lp, l, xt, yt)), N.Int.mul(N.Int.mul(N.Int.mul(N.Pos{2n}, lp), mden(q2, s2, lp)), N.Int.add(N.Int.mul(uexp(p, q, s, p2, q2, s2), rxexp(p, q, r, s, lp, PG.rest(l, xt, yt))), N.Int.mul(vexp(r, q, s, r2, q2, s2, lp), rexp(p, q, r, s, lp, PG.rest(l, xt, yt)))))), N.Int.mul(N.Int.mul(lp, lp), w2(uexp(p, q, s, p2, q2, s2), vexp(r, q, s, r2, q2, s2, lp), PG.rest(l, xt, yt)))), key(lp, p, q, r, s, p2, q2, r2, s2, l, xt, yt))
           : {N.Int.add(N.Int.mul(N.Int.mul(rterm(p2, q2, r2, s2, lp, L.Stats.scale(l, x), L.Stats.scale(l, y)), mden(q, s, lp)), N.Int.mul(rterm(p2, q2, r2, s2, lp, L.Stats.scale(l, x), L.Stats.scale(l, y)), mden(q, s, lp))), _) == N.Int.add(N.Int.add(N.Int.mul(N.Int.mul(mden(q2, s2, lp), mden(q2, s2, lp)), N.Int.add(PG.sq(rterm(p, q, r, s, lp, L.Stats.scale(l, x), L.Stats.scale(l, y))), sumsq(p, q, r, s, lp, l, xt, yt))), N.Int.mul(N.Int.mul(N.Int.mul(N.Pos{2n}, lp), mden(q2, s2, lp)), N.Int.add(N.Int.mul(uexp(p, q, s, p2, q2, s2), N.Int.add(N.Int.mul(L.Stats.scale(l, x), rterm(p, q, r, s, lp, L.Stats.scale(l, x), L.Stats.scale(l, y))), rxexp(p, q, r, s, lp, PG.rest(l, xt, yt)))), N.Int.mul(vexp(r, q, s, r2, q2, s2, lp), N.Int.add(rterm(p, q, r, s, lp, L.Stats.scale(l, x), L.Stats.scale(l, y)), rexp(p, q, r, s, lp, PG.rest(l, xt, yt))))))), N.Int.mul(N.Int.mul(lp, lp), N.Int.add(PG.sq(wt(uexp(p, q, s, p2, q2, s2), vexp(r, q, s, r2, q2, s2, lp), L.Stats.scale(l, x))), w2(uexp(p, q, s, p2, q2, s2), vexp(r, q, s, r2, q2, s2, lp), PG.rest(l, xt, yt))))) : N.Int}
         %Equal.sym(N.Int, N.Int.mul(rterm(p2, q2, r2, s2, lp, L.Stats.scale(l, x), L.Stats.scale(l, y)), mden(q, s, lp)), N.Int.add(N.Int.mul(rterm(p, q, r, s, lp, L.Stats.scale(l, x), L.Stats.scale(l, y)), mden(q2, s2, lp)), N.Int.mul(lp, wt(uexp(p, q, s, p2, q2, s2), vexp(r, q, s, r2, q2, s2, lp), L.Stats.scale(l, x)))),
             lin(lp, p, q, r, s, p2, q2, r2, s2, L.Stats.scale(l, x), L.Stats.scale(l, y)))
           : {N.Int.add(N.Int.mul(_, _), N.Int.add(N.Int.add(N.Int.mul(N.Int.mul(mden(q2, s2, lp), mden(q2, s2, lp)), sumsq(p, q, r, s, lp, l, xt, yt)), N.Int.mul(N.Int.mul(N.Int.mul(N.Pos{2n}, lp), mden(q2, s2, lp)), N.Int.add(N.Int.mul(uexp(p, q, s, p2, q2, s2), rxexp(p, q, r, s, lp, PG.rest(l, xt, yt))), N.Int.mul(vexp(r, q, s, r2, q2, s2, lp), rexp(p, q, r, s, lp, PG.rest(l, xt, yt)))))), N.Int.mul(N.Int.mul(lp, lp), w2(uexp(p, q, s, p2, q2, s2), vexp(r, q, s, r2, q2, s2, lp), PG.rest(l, xt, yt))))) == N.Int.add(N.Int.add(N.Int.mul(N.Int.mul(mden(q2, s2, lp), mden(q2, s2, lp)), N.Int.add(PG.sq(rterm(p, q, r, s, lp, L.Stats.scale(l, x), L.Stats.scale(l, y))), sumsq(p, q, r, s, lp, l, xt, yt))), N.Int.mul(N.Int.mul(N.Int.mul(N.Pos{2n}, lp), mden(q2, s2, lp)), N.Int.add(N.Int.mul(uexp(p, q, s, p2, q2, s2), N.Int.add(N.Int.mul(L.Stats.scale(l, x), rterm(p, q, r, s, lp, L.Stats.scale(l, x), L.Stats.scale(l, y))), rxexp(p, q, r, s, lp, PG.rest(l, xt, yt)))), N.Int.mul(vexp(r, q, s, r2, q2, s2, lp), N.Int.add(rterm(p, q, r, s, lp, L.Stats.scale(l, x), L.Stats.scale(l, y)), rexp(p, q, r, s, lp, PG.rest(l, xt, yt))))))), N.Int.mul(N.Int.mul(lp, lp), N.Int.add(PG.sq(wt(uexp(p, q, s, p2, q2, s2), vexp(r, q, s, r2, q2, s2, lp), L.Stats.scale(l, x))), w2(uexp(p, q, s, p2, q2, s2), vexp(r, q, s, r2, q2, s2, lp), PG.rest(l, xt, yt))))) : N.Int}
         PI.IRing.eq(PI.IAdd{PI.IMul{PI.IAdd{PI.IMul{PI.IVar{0n}, PI.IVar{1n}}, PI.IMul{PI.IVar{2n}, PI.IAdd{PI.IMul{PI.IVar{3n}, PI.IVar{5n}}, PI.IVar{4n}}}}, PI.IAdd{PI.IMul{PI.IVar{0n}, PI.IVar{1n}}, PI.IMul{PI.IVar{2n}, PI.IAdd{PI.IMul{PI.IVar{3n}, PI.IVar{5n}}, PI.IVar{4n}}}}}, PI.IAdd{PI.IAdd{PI.IMul{PI.IMul{PI.IVar{1n}, PI.IVar{1n}}, PI.IVar{6n}}, PI.IMul{PI.IMul{PI.IMul{PI.IConst{N.Pos{2n}}, PI.IVar{2n}}, PI.IVar{1n}}, PI.IAdd{PI.IMul{PI.IVar{3n}, PI.IVar{7n}}, PI.IMul{PI.IVar{4n}, PI.IVar{8n}}}}}, PI.IMul{PI.IMul{PI.IVar{2n}, PI.IVar{2n}}, PI.IVar{9n}}}}, PI.IAdd{PI.IAdd{PI.IMul{PI.IMul{PI.IVar{1n}, PI.IVar{1n}}, PI.IAdd{PI.IMul{PI.IVar{0n}, PI.IVar{0n}}, PI.IVar{6n}}}, PI.IMul{PI.IMul{PI.IMul{PI.IConst{N.Pos{2n}}, PI.IVar{2n}}, PI.IVar{1n}}, PI.IAdd{PI.IMul{PI.IVar{3n}, PI.IAdd{PI.IMul{PI.IVar{5n}, PI.IVar{0n}}, PI.IVar{7n}}}, PI.IMul{PI.IVar{4n}, PI.IAdd{PI.IVar{0n}, PI.IVar{8n}}}}}}, PI.IMul{PI.IMul{PI.IVar{2n}, PI.IVar{2n}}, PI.IAdd{PI.IMul{PI.IAdd{PI.IMul{PI.IVar{3n}, PI.IVar{5n}}, PI.IVar{4n}}, PI.IAdd{PI.IMul{PI.IVar{3n}, PI.IVar{5n}}, PI.IVar{4n}}}, PI.IVar{9n}}}}, [rterm(p, q, r, s, lp, L.Stats.scale(l, x), L.Stats.scale(l, y)), mden(q2, s2, lp), lp, uexp(p, q, s, p2, q2, s2), vexp(r, q, s, r2, q2, s2, lp), L.Stats.scale(l, x), sumsq(p, q, r, s, lp, l, xt, yt), rxexp(p, q, r, s, lp, PG.rest(l, xt, yt)), rexp(p, q, r, s, lp, PG.rest(l, xt, yt)), w2(uexp(p, q, s, p2, q2, s2), vexp(r, q, s, r2, q2, s2, lp), PG.rest(l, xt, yt))], {==})))

law isp_mul:
  for +a: N.Int
  for +b: N.Int
  for ha: PR.Int.isp(a)
  for hb: PR.Int.isp(b)
  PR.Int.isp(N.Int.mul(a, b))

def isp_mul(a, b, ha, hb):
  match a b:
    case N.Pos{m} N.Pos{n}:
      Unit{}
    case N.Pos{m} N.Neg{n}:
      match hb:
    case N.Neg{m} _:
      match ha:

law cross1:
  for +u: N.Int
  for +a: N.Int
  for +k1: N.Int
  for +k2: N.Int
  for +d1: N.Int
  for +d2: N.Int
  for +h: {N.Int.mul(u, k1) == N.Int.mul(a, d1) : N.Int}
  {N.Int.mul(N.Int.mul(u, d2), N.Int.mul(k1, k2)) == N.Int.mul(N.Int.mul(a, k2), N.Int.mul(d1, d2)) : N.Int}

def cross1(u, a, k1, k2, d1, d2, h):
  Equal.trans(N.Int, N.Int.mul(N.Int.mul(u, d2), N.Int.mul(k1, k2)), N.Int.mul(N.Int.mul(u, k1), N.Int.mul(d2, k2)),
    N.Int.mul(N.Int.mul(a, k2), N.Int.mul(d1, d2)),
    PI.IRing.eq(PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{3n}}, PI.IMul{PI.IVar{1n}, PI.IVar{2n}}}, PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{1n}}, PI.IMul{PI.IVar{3n}, PI.IVar{2n}}}, [u, k1, k2, d2], {==}),
    (%Equal.sym(N.Int, N.Int.mul(u, k1), N.Int.mul(a, d1), h)
       : {N.Int.mul(_, N.Int.mul(d2, k2)) == N.Int.mul(N.Int.mul(a, k2), N.Int.mul(d1, d2)) : N.Int}
     PI.IRing.eq(PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{1n}}, PI.IMul{PI.IVar{2n}, PI.IVar{3n}}}, PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{3n}}, PI.IMul{PI.IVar{1n}, PI.IVar{2n}}}, [a, d1, d2, k2], {==})))

law cross2:
  for +u: N.Int
  for +a: N.Int
  for +k1: N.Int
  for +k2: N.Int
  for +d1: N.Int
  for +d2: N.Int
  for +h: {N.Int.mul(u, k2) == N.Int.mul(a, d2) : N.Int}
  {N.Int.mul(N.Int.mul(u, d1), N.Int.mul(k1, k2)) == N.Int.mul(N.Int.mul(a, k1), N.Int.mul(d1, d2)) : N.Int}

def cross2(u, a, k1, k2, d1, d2, h):
  Equal.trans(N.Int, N.Int.mul(N.Int.mul(u, d1), N.Int.mul(k1, k2)), N.Int.mul(N.Int.mul(u, k2), N.Int.mul(d1, k1)),
    N.Int.mul(N.Int.mul(a, k1), N.Int.mul(d1, d2)),
    PI.IRing.eq(PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{3n}}, PI.IMul{PI.IVar{1n}, PI.IVar{2n}}}, PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{2n}}, PI.IMul{PI.IVar{3n}, PI.IVar{1n}}}, [u, k1, k2, d1], {==}),
    (%Equal.sym(N.Int, N.Int.mul(u, k2), N.Int.mul(a, d2), h)
       : {N.Int.mul(_, N.Int.mul(d1, k1)) == N.Int.mul(N.Int.mul(a, k1), N.Int.mul(d1, d2)) : N.Int}
     PI.IRing.eq(PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{2n}}, PI.IMul{PI.IVar{1n}, PI.IVar{3n}}}, PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{3n}}, PI.IMul{PI.IVar{1n}, PI.IVar{2n}}}, [a, d1, d2, k1], {==})))

# e1 == a1 / k1 and e2 == a2 / k2: comparing the Rats is comparing a1 k2 and a2 k1
law rat_le_of:
  for e1: N.Rat
  for e2: N.Rat
  for +a1: N.Int
  for +k1: Nat
  for +a2: N.Int
  for +k2: Nat
  for h1: Laws.Denotes(e1, a1, N.Pos{1n+k1})
  for h2: Laws.Denotes(e2, a2, N.Pos{1n+k2})
  for +hle: {N.Int.is_le(N.Int.mul(a1, N.Pos{1n+k2}), N.Int.mul(a2, N.Pos{1n+k1})) == True{} : Bool}
  {N.Rat.is_le(e1, e2) == True{} : Bool}

def rat_le_of(e1, e2, a1, k1, a2, k2, h1, h2, hle):
  match e1 e2:
    case N.Rat{+u1, +d1} N.Rat{+u2, +d2}:
      le_cancel(N.Int.mul(u1, N.Pos{1n+d2}), N.Int.mul(u2, N.Pos{1n+d1}), N.Nat.mul_pred(k1, k2),
        (%Equal.sym(N.Int, N.Int.mul(N.Int.mul(u1, N.Pos{1n+d2}), N.Int.mul(N.Pos{1n+k1}, N.Pos{1n+k2})),
             N.Int.mul(N.Int.mul(a1, N.Pos{1n+k2}), N.Int.mul(N.Pos{1n+d1}, N.Pos{1n+d2})),
             cross1(u1, a1, N.Pos{1n+k1}, N.Pos{1n+k2}, N.Pos{1n+d1}, N.Pos{1n+d2}, h1))
           : {N.Int.is_le(_, N.Int.mul(N.Int.mul(u2, N.Pos{1n+d1}), N.Pos{1n+N.Nat.mul_pred(k1, k2)})) == True{} : Bool}
         %Equal.sym(N.Int, N.Int.mul(N.Int.mul(u2, N.Pos{1n+d1}), N.Int.mul(N.Pos{1n+k1}, N.Pos{1n+k2})),
             N.Int.mul(N.Int.mul(a2, N.Pos{1n+k1}), N.Int.mul(N.Pos{1n+d1}, N.Pos{1n+d2})),
             cross2(u2, a2, N.Pos{1n+k1}, N.Pos{1n+k2}, N.Pos{1n+d1}, N.Pos{1n+d2}, h2))
           : {N.Int.is_le(N.Int.mul(N.Int.mul(a1, N.Pos{1n+k2}), N.Pos{1n+N.Nat.mul_pred(d1, d2)}), _) == True{} : Bool}
         le_mul_pos(N.Int.mul(a1, N.Pos{1n+k2}), N.Int.mul(a2, N.Pos{1n+k1}), N.Nat.mul_pred(d1, d2), hle)))

law rat_le_to:
  for e1: N.Rat
  for e2: N.Rat
  for +a1: N.Int
  for +k1: Nat
  for +a2: N.Int
  for +k2: Nat
  for h1: Laws.Denotes(e1, a1, N.Pos{1n+k1})
  for h2: Laws.Denotes(e2, a2, N.Pos{1n+k2})
  for +h: {N.Rat.is_le(e1, e2) == True{} : Bool}
  {N.Int.is_le(N.Int.mul(a1, N.Pos{1n+k2}), N.Int.mul(a2, N.Pos{1n+k1})) == True{} : Bool}

def rat_le_to(e1, e2, a1, k1, a2, k2, h1, h2, h):
  match e1 e2:
    case N.Rat{+u1, +d1} N.Rat{+u2, +d2}:
      le_cancel(N.Int.mul(a1, N.Pos{1n+k2}), N.Int.mul(a2, N.Pos{1n+k1}), N.Nat.mul_pred(d1, d2),
        (%cross1(u1, a1, N.Pos{1n+k1}, N.Pos{1n+k2}, N.Pos{1n+d1}, N.Pos{1n+d2}, h1)
           : {N.Int.is_le(_, N.Int.mul(N.Int.mul(a2, N.Pos{1n+k1}), N.Pos{1n+N.Nat.mul_pred(d1, d2)})) == True{} : Bool}
         %cross2(u2, a2, N.Pos{1n+k1}, N.Pos{1n+k2}, N.Pos{1n+d1}, N.Pos{1n+d2}, h2)
           : {N.Int.is_le(N.Int.mul(N.Int.mul(u1, N.Pos{1n+d2}), N.Pos{1n+N.Nat.mul_pred(k1, k2)}), _) == True{} : Bool}
         le_mul_pos(N.Int.mul(u1, N.Pos{1n+d2}), N.Int.mul(u2, N.Pos{1n+d1}), N.Nat.mul_pred(k1, k2), h)))

# the cross term vanishes
law key_zero:
  for +lp: N.Int
  for +p: N.Int
  for +q: N.Int
  for +r: N.Int
  for +s: N.Int
  for +p2: N.Int
  for +q2: N.Int
  for +r2: N.Int
  for +s2: N.Int
  for +l: Nat
  for +xs: +List<N.Rat>
  for +ys: +List<N.Rat>
  for +e0: {N.Int.add(N.Int.mul(uexp(p, q, s, p2, q2, s2), rxexp(p, q, r, s, lp, PG.rest(l, xs, ys))), N.Int.mul(vexp(r, q, s, r2, q2, s2, lp), rexp(p, q, r, s, lp, PG.rest(l, xs, ys)))) == N.Pos{0n} : N.Int}
  {N.Int.mul(N.Int.mul(mden(q, s, lp), mden(q, s, lp)), sumsq(p2, q2, r2, s2, lp, l, xs, ys)) == N.Int.add(N.Int.mul(N.Int.mul(mden(q2, s2, lp), mden(q2, s2, lp)), sumsq(p, q, r, s, lp, l, xs, ys)), N.Int.mul(N.Int.mul(lp, lp), w2(uexp(p, q, s, p2, q2, s2), vexp(r, q, s, r2, q2, s2, lp), PG.rest(l, xs, ys)))) : N.Int}

def key_zero(lp, p, q, r, s, p2, q2, r2, s2, l, xs, ys, e0):
  Equal.trans(N.Int, N.Int.mul(N.Int.mul(mden(q, s, lp), mden(q, s, lp)), sumsq(p2, q2, r2, s2, lp, l, xs, ys)), N.Int.add(N.Int.add(N.Int.mul(N.Int.mul(mden(q2, s2, lp), mden(q2, s2, lp)), sumsq(p, q, r, s, lp, l, xs, ys)), N.Int.mul(N.Int.mul(N.Int.mul(N.Pos{2n}, lp), mden(q2, s2, lp)), N.Int.add(N.Int.mul(uexp(p, q, s, p2, q2, s2), rxexp(p, q, r, s, lp, PG.rest(l, xs, ys))), N.Int.mul(vexp(r, q, s, r2, q2, s2, lp), rexp(p, q, r, s, lp, PG.rest(l, xs, ys)))))), N.Int.mul(N.Int.mul(lp, lp), w2(uexp(p, q, s, p2, q2, s2), vexp(r, q, s, r2, q2, s2, lp), PG.rest(l, xs, ys)))), N.Int.add(N.Int.mul(N.Int.mul(mden(q2, s2, lp), mden(q2, s2, lp)), sumsq(p, q, r, s, lp, l, xs, ys)), N.Int.mul(N.Int.mul(lp, lp), w2(uexp(p, q, s, p2, q2, s2), vexp(r, q, s, r2, q2, s2, lp), PG.rest(l, xs, ys)))),
    key(lp, p, q, r, s, p2, q2, r2, s2, l, xs, ys),
    (%Equal.sym(N.Int, N.Int.add(N.Int.mul(uexp(p, q, s, p2, q2, s2), rxexp(p, q, r, s, lp, PG.rest(l, xs, ys))), N.Int.mul(vexp(r, q, s, r2, q2, s2, lp), rexp(p, q, r, s, lp, PG.rest(l, xs, ys)))), N.Pos{0n}, e0)
       : {N.Int.add(N.Int.add(N.Int.mul(N.Int.mul(mden(q2, s2, lp), mden(q2, s2, lp)), sumsq(p, q, r, s, lp, l, xs, ys)), N.Int.mul(N.Int.mul(N.Int.mul(N.Pos{2n}, lp), mden(q2, s2, lp)), _)), N.Int.mul(N.Int.mul(lp, lp), w2(uexp(p, q, s, p2, q2, s2), vexp(r, q, s, r2, q2, s2, lp), PG.rest(l, xs, ys)))) == N.Int.add(N.Int.mul(N.Int.mul(mden(q2, s2, lp), mden(q2, s2, lp)), sumsq(p, q, r, s, lp, l, xs, ys)), N.Int.mul(N.Int.mul(lp, lp), w2(uexp(p, q, s, p2, q2, s2), vexp(r, q, s, r2, q2, s2, lp), PG.rest(l, xs, ys)))) : N.Int}
     PI.IRing.eq(PI.IAdd{PI.IAdd{PI.IVar{0n}, PI.IMul{PI.IVar{1n}, PI.IConst{N.Pos{0n}}}}, PI.IVar{2n}}, PI.IAdd{PI.IVar{0n}, PI.IVar{2n}}, [N.Int.mul(N.Int.mul(mden(q2, s2, lp), mden(q2, s2, lp)), sumsq(p, q, r, s, lp, l, xs, ys)), N.Int.mul(N.Int.mul(N.Pos{2n}, lp), mden(q2, s2, lp)), N.Int.mul(N.Int.mul(lp, lp), w2(uexp(p, q, s, p2, q2, s2), vexp(r, q, s, r2, q2, s2, lp), PG.rest(l, xs, ys)))], {==})))

law ls_e3:
  for +l: Nat
  for +lp: Nat
  for +hl: {l == 1n+lp : Nat}
  for +p: N.Int
  for +qa: Nat
  for +r: N.Int
  for +sb: Nat
  for +p2: N.Int
  for +qa2: Nat
  for +r2: N.Int
  for +sb2: Nat
  for +xs: +List<N.Rat>
  for +ys: +List<N.Rat>
  for +hx: {PG.dvb(xs, l) == True{} : Bool}
  for +hy: {PG.dvb(ys, l) == True{} : Bool}
  for +e: {N.Int.mul(N.Int.mul(mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp}), mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp})), sumsq(p2, N.Pos{1n+qa2}, r2, N.Pos{1n+sb2}, N.Pos{1n+lp}, l, xs, ys)) == N.Int.add(N.Int.mul(N.Int.mul(mden(N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), mden(N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp})), sumsq(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, l, xs, ys)), N.Int.mul(N.Int.mul(N.Pos{1n+lp}, N.Pos{1n+lp}), w2(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), PG.rest(l, xs, ys)))) : N.Int}
  for +c: Nat
  for +ec: {N.Int.mul(N.Int.mul(N.Pos{1n+lp}, N.Pos{1n+lp}), w2(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), PG.rest(l, xs, ys))) == N.Pos{c} : N.Int}
  {N.Int.mul(sumsq(p2, N.Pos{1n+qa2}, r2, N.Pos{1n+sb2}, N.Pos{1n+lp}, l, xs, ys), N.Pos{1n+N.Nat.mul_pred(N.Nat.mul_pred(N.Nat.mul_pred(lp, qa), sb), N.Nat.mul_pred(N.Nat.mul_pred(lp, qa), sb))}) == N.Int.add(N.Int.mul(sumsq(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, l, xs, ys), N.Pos{1n+N.Nat.mul_pred(N.Nat.mul_pred(N.Nat.mul_pred(lp, qa2), sb2), N.Nat.mul_pred(N.Nat.mul_pred(lp, qa2), sb2))}), N.Pos{c}) : N.Int}

def ls_e3(l, lp, hl, p, qa, r, sb, p2, qa2, r2, sb2, xs, ys, hx, hy, e, c, ec):
  Equal.trans(N.Int, N.Int.mul(sumsq(p2, N.Pos{1n+qa2}, r2, N.Pos{1n+sb2}, N.Pos{1n+lp}, l, xs, ys), N.Pos{1n+N.Nat.mul_pred(N.Nat.mul_pred(N.Nat.mul_pred(lp, qa), sb), N.Nat.mul_pred(N.Nat.mul_pred(lp, qa), sb))}), N.Int.mul(N.Int.mul(mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp}), mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp})), sumsq(p2, N.Pos{1n+qa2}, r2, N.Pos{1n+sb2}, N.Pos{1n+lp}, l, xs, ys)), N.Int.add(N.Int.mul(sumsq(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, l, xs, ys), N.Pos{1n+N.Nat.mul_pred(N.Nat.mul_pred(N.Nat.mul_pred(lp, qa2), sb2), N.Nat.mul_pred(N.Nat.mul_pred(lp, qa2), sb2))}), N.Pos{c}),
    PI.IRing.eq(PI.IMul{PI.IVar{0n}, PI.IMul{PI.IVar{1n}, PI.IVar{1n}}}, PI.IMul{PI.IMul{PI.IVar{1n}, PI.IVar{1n}}, PI.IVar{0n}}, [sumsq(p2, N.Pos{1n+qa2}, r2, N.Pos{1n+sb2}, N.Pos{1n+lp}, l, xs, ys), mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp})], {==}),
    Equal.trans(N.Int, N.Int.mul(N.Int.mul(mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp}), mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp})), sumsq(p2, N.Pos{1n+qa2}, r2, N.Pos{1n+sb2}, N.Pos{1n+lp}, l, xs, ys)), N.Int.add(N.Int.mul(N.Int.mul(mden(N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), mden(N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp})), sumsq(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, l, xs, ys)), N.Int.mul(N.Int.mul(N.Pos{1n+lp}, N.Pos{1n+lp}), w2(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), PG.rest(l, xs, ys)))),
      N.Int.add(N.Int.mul(sumsq(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, l, xs, ys), N.Pos{1n+N.Nat.mul_pred(N.Nat.mul_pred(N.Nat.mul_pred(lp, qa2), sb2), N.Nat.mul_pred(N.Nat.mul_pred(lp, qa2), sb2))}), N.Pos{c}),
      e,
      (%Equal.sym(N.Int, N.Int.mul(N.Int.mul(N.Pos{1n+lp}, N.Pos{1n+lp}), w2(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), PG.rest(l, xs, ys))), N.Pos{c}, ec)
         : {N.Int.add(N.Int.mul(N.Int.mul(mden(N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), mden(N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp})), sumsq(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, l, xs, ys)), _) == N.Int.add(N.Int.mul(sumsq(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, l, xs, ys), N.Pos{1n+N.Nat.mul_pred(N.Nat.mul_pred(N.Nat.mul_pred(lp, qa2), sb2), N.Nat.mul_pred(N.Nat.mul_pred(lp, qa2), sb2))}), N.Pos{c}) : N.Int}
       PI.IRing.eq(PI.IAdd{PI.IMul{PI.IMul{PI.IVar{1n}, PI.IVar{1n}}, PI.IVar{0n}}, PI.IVar{2n}}, PI.IAdd{PI.IMul{PI.IVar{0n}, PI.IMul{PI.IVar{1n}, PI.IVar{1n}}}, PI.IVar{2n}}, [sumsq(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, l, xs, ys), mden(N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), N.Pos{c}], {==}))))

law ls_le.c:
  for +l: Nat
  for +lp: Nat
  for +hl: {l == 1n+lp : Nat}
  for +p: N.Int
  for +qa: Nat
  for +r: N.Int
  for +sb: Nat
  for +p2: N.Int
  for +qa2: Nat
  for +r2: N.Int
  for +sb2: Nat
  for +xs: +List<N.Rat>
  for +ys: +List<N.Rat>
  for +hx: {PG.dvb(xs, l) == True{} : Bool}
  for +hy: {PG.dvb(ys, l) == True{} : Bool}
  for +e: {N.Int.mul(N.Int.mul(mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp}), mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp})), sumsq(p2, N.Pos{1n+qa2}, r2, N.Pos{1n+sb2}, N.Pos{1n+lp}, l, xs, ys)) == N.Int.add(N.Int.mul(N.Int.mul(mden(N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), mden(N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp})), sumsq(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, l, xs, ys)), N.Int.mul(N.Int.mul(N.Pos{1n+lp}, N.Pos{1n+lp}), w2(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), PG.rest(l, xs, ys)))) : N.Int}
  for +c: Nat
  for +ec: {N.Int.mul(N.Int.mul(N.Pos{1n+lp}, N.Pos{1n+lp}), w2(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), PG.rest(l, xs, ys))) == N.Pos{c} : N.Int}
  {N.Rat.is_le(Laws.sse(N.Rat{p, qa}, N.Rat{r, sb}, xs, ys), Laws.sse(N.Rat{p2, qa2}, N.Rat{r2, sb2}, xs, ys)) == True{} : Bool}

def ls_le.c(l, lp, hl, p, qa, r, sb, p2, qa2, r2, sb2, xs, ys, hx, hy, e, c, ec):
  rat_le_of(Laws.sse(N.Rat{p, qa}, N.Rat{r, sb}, xs, ys), Laws.sse(N.Rat{p2, qa2}, N.Rat{r2, sb2}, xs, ys), sumsq(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, l, xs, ys), N.Nat.mul_pred(N.Nat.mul_pred(N.Nat.mul_pred(lp, qa), sb), N.Nat.mul_pred(N.Nat.mul_pred(lp, qa), sb)), sumsq(p2, N.Pos{1n+qa2}, r2, N.Pos{1n+sb2}, N.Pos{1n+lp}, l, xs, ys), N.Nat.mul_pred(N.Nat.mul_pred(N.Nat.mul_pred(lp, qa2), sb2), N.Nat.mul_pred(N.Nat.mul_pred(lp, qa2), sb2)), sse_den(l, lp, hl, p, qa, r, sb, xs, ys, hx, hy), sse_den(l, lp, hl, p2, qa2, r2, sb2, xs, ys, hx, hy),
    (%Equal.sym(N.Int, N.Int.mul(sumsq(p2, N.Pos{1n+qa2}, r2, N.Pos{1n+sb2}, N.Pos{1n+lp}, l, xs, ys), N.Pos{1n+N.Nat.mul_pred(N.Nat.mul_pred(N.Nat.mul_pred(lp, qa), sb), N.Nat.mul_pred(N.Nat.mul_pred(lp, qa), sb))}), N.Int.add(N.Int.mul(sumsq(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, l, xs, ys), N.Pos{1n+N.Nat.mul_pred(N.Nat.mul_pred(N.Nat.mul_pred(lp, qa2), sb2), N.Nat.mul_pred(N.Nat.mul_pred(lp, qa2), sb2))}), N.Pos{c}), ls_e3(l, lp, hl, p, qa, r, sb, p2, qa2, r2, sb2, xs, ys, hx, hy, e, c, ec))
       : {N.Int.is_le(N.Int.mul(sumsq(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, l, xs, ys), N.Pos{1n+N.Nat.mul_pred(N.Nat.mul_pred(N.Nat.mul_pred(lp, qa2), sb2), N.Nat.mul_pred(N.Nat.mul_pred(lp, qa2), sb2))}), _) == True{} : Bool}
     le_of_add(N.Int.mul(sumsq(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, l, xs, ys), N.Pos{1n+N.Nat.mul_pred(N.Nat.mul_pred(N.Nat.mul_pred(lp, qa2), sb2), N.Nat.mul_pred(N.Nat.mul_pred(lp, qa2), sb2))}), c)))

law ls_le.w:
  for +l: Nat
  for +lp: Nat
  for +hl: {l == 1n+lp : Nat}
  for +p: N.Int
  for +qa: Nat
  for +r: N.Int
  for +sb: Nat
  for +p2: N.Int
  for +qa2: Nat
  for +r2: N.Int
  for +sb2: Nat
  for +xs: +List<N.Rat>
  for +ys: +List<N.Rat>
  for +hx: {PG.dvb(xs, l) == True{} : Bool}
  for +hy: {PG.dvb(ys, l) == True{} : Bool}
  for +e: {N.Int.mul(N.Int.mul(mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp}), mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp})), sumsq(p2, N.Pos{1n+qa2}, r2, N.Pos{1n+sb2}, N.Pos{1n+lp}, l, xs, ys)) == N.Int.add(N.Int.mul(N.Int.mul(mden(N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), mden(N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp})), sumsq(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, l, xs, ys)), N.Int.mul(N.Int.mul(N.Pos{1n+lp}, N.Pos{1n+lp}), w2(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), PG.rest(l, xs, ys)))) : N.Int}
  for w: &c: Nat -> {N.Int.mul(N.Int.mul(N.Pos{1n+lp}, N.Pos{1n+lp}), w2(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), PG.rest(l, xs, ys))) == N.Pos{c} : N.Int}
  {N.Rat.is_le(Laws.sse(N.Rat{p, qa}, N.Rat{r, sb}, xs, ys), Laws.sse(N.Rat{p2, qa2}, N.Rat{r2, sb2}, xs, ys)) == True{} : Bool}

def ls_le.w(l, lp, hl, p, qa, r, sb, p2, qa2, r2, sb2, xs, ys, hx, hy, e, w):
  match w:
    case (+c, ec):
      ls_le.c(l, lp, hl, p, qa, r, sb, p2, qa2, r2, sb2, xs, ys, hx, hy, e, c, ec)

law w_pos:
  for +l: Nat
  for +lp: Nat
  for +hl: {l == 1n+lp : Nat}
  for +p: N.Int
  for +qa: Nat
  for +r: N.Int
  for +sb: Nat
  for +p2: N.Int
  for +qa2: Nat
  for +r2: N.Int
  for +sb2: Nat
  for +xs: +List<N.Rat>
  for +ys: +List<N.Rat>
  for +hx: {PG.dvb(xs, l) == True{} : Bool}
  for +hy: {PG.dvb(ys, l) == True{} : Bool}
  exs c: Nat
  {N.Int.mul(N.Int.mul(N.Pos{1n+lp}, N.Pos{1n+lp}), w2(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), PG.rest(l, xs, ys))) == N.Pos{c} : N.Int}

def w_pos(l, lp, hl, p, qa, r, sb, p2, qa2, r2, sb2, xs, ys, hx, hy):
  isp_pos(N.Int.mul(N.Int.mul(N.Pos{1n+lp}, N.Pos{1n+lp}), w2(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), PG.rest(l, xs, ys))),
    isp_mul(N.Int.mul(N.Pos{1n+lp}, N.Pos{1n+lp}), w2(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), PG.rest(l, xs, ys)), PG.isp_sq(N.Pos{1n+lp}), w2_nonneg(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), l, L.Point.zip(xs, ys))))

# the fitted line's SSE is at most any other line's
law ls_le:
  for +l: Nat
  for +lp: Nat
  for +hl: {l == 1n+lp : Nat}
  for +p: N.Int
  for +qa: Nat
  for +r: N.Int
  for +sb: Nat
  for +p2: N.Int
  for +qa2: Nat
  for +r2: N.Int
  for +sb2: Nat
  for +xs: +List<N.Rat>
  for +ys: +List<N.Rat>
  for +hx: {PG.dvb(xs, l) == True{} : Bool}
  for +hy: {PG.dvb(ys, l) == True{} : Bool}
  for +e: {N.Int.mul(N.Int.mul(mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp}), mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp})), sumsq(p2, N.Pos{1n+qa2}, r2, N.Pos{1n+sb2}, N.Pos{1n+lp}, l, xs, ys)) == N.Int.add(N.Int.mul(N.Int.mul(mden(N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), mden(N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp})), sumsq(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, l, xs, ys)), N.Int.mul(N.Int.mul(N.Pos{1n+lp}, N.Pos{1n+lp}), w2(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), PG.rest(l, xs, ys)))) : N.Int}
  {N.Rat.is_le(Laws.sse(N.Rat{p, qa}, N.Rat{r, sb}, xs, ys), Laws.sse(N.Rat{p2, qa2}, N.Rat{r2, sb2}, xs, ys)) == True{} : Bool}

def ls_le(l, lp, hl, p, qa, r, sb, p2, qa2, r2, sb2, xs, ys, hx, hy, e):
  ls_le.w(l, lp, hl, p, qa, r, sb, p2, qa2, r2, sb2, xs, ys, hx, hy, e, w_pos(l, lp, hl, p, qa, r, sb, p2, qa2, r2, sb2, xs, ys, hx, hy))

law ls_w2.c:
  for +l: Nat
  for +lp: Nat
  for +hl: {l == 1n+lp : Nat}
  for +p: N.Int
  for +qa: Nat
  for +r: N.Int
  for +sb: Nat
  for +p2: N.Int
  for +qa2: Nat
  for +r2: N.Int
  for +sb2: Nat
  for +xs: +List<N.Rat>
  for +ys: +List<N.Rat>
  for +hx: {PG.dvb(xs, l) == True{} : Bool}
  for +hy: {PG.dvb(ys, l) == True{} : Bool}
  for +e: {N.Int.mul(N.Int.mul(mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp}), mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp})), sumsq(p2, N.Pos{1n+qa2}, r2, N.Pos{1n+sb2}, N.Pos{1n+lp}, l, xs, ys)) == N.Int.add(N.Int.mul(N.Int.mul(mden(N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), mden(N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp})), sumsq(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, l, xs, ys)), N.Int.mul(N.Int.mul(N.Pos{1n+lp}, N.Pos{1n+lp}), w2(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), PG.rest(l, xs, ys)))) : N.Int}
  for +good: {N.Rat.is_le(Laws.sse(N.Rat{p2, qa2}, N.Rat{r2, sb2}, xs, ys), Laws.sse(N.Rat{p, qa}, N.Rat{r, sb}, xs, ys)) == True{} : Bool}
  for +c: Nat
  for +ec: {N.Int.mul(N.Int.mul(N.Pos{1n+lp}, N.Pos{1n+lp}), w2(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), PG.rest(l, xs, ys))) == N.Pos{c} : N.Int}
  {w2(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), PG.rest(l, xs, ys)) == N.Pos{0n} : N.Int}

def ls_w2.c(l, lp, hl, p, qa, r, sb, p2, qa2, r2, sb2, xs, ys, hx, hy, e, good, c, ec):
  mul_eq_zero(w2(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), PG.rest(l, xs, ys)), N.Int.mul(N.Pos{1n+lp}, N.Pos{1n+lp}),
    Equal.trans(N.Int, N.Int.mul(w2(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), PG.rest(l, xs, ys)), N.Int.mul(N.Pos{1n+lp}, N.Pos{1n+lp})), N.Int.mul(N.Int.mul(N.Pos{1n+lp}, N.Pos{1n+lp}), w2(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), PG.rest(l, xs, ys))), N.Pos{0n},
      PI.IRing.eq(PI.IMul{PI.IVar{0n}, PI.IMul{PI.IVar{1n}, PI.IVar{1n}}}, PI.IMul{PI.IMul{PI.IVar{1n}, PI.IVar{1n}}, PI.IVar{0n}}, [w2(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), PG.rest(l, xs, ys)), N.Pos{1n+lp}], {==}),
      (%le_add_zero(N.Int.mul(sumsq(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, l, xs, ys), N.Pos{1n+N.Nat.mul_pred(N.Nat.mul_pred(N.Nat.mul_pred(lp, qa2), sb2), N.Nat.mul_pred(N.Nat.mul_pred(lp, qa2), sb2))}), c,
           (%ls_e3(l, lp, hl, p, qa, r, sb, p2, qa2, r2, sb2, xs, ys, hx, hy, e, c, ec) : {N.Int.is_le(_, N.Int.mul(sumsq(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, l, xs, ys), N.Pos{1n+N.Nat.mul_pred(N.Nat.mul_pred(N.Nat.mul_pred(lp, qa2), sb2), N.Nat.mul_pred(N.Nat.mul_pred(lp, qa2), sb2))})) == True{} : Bool}
            rat_le_to(Laws.sse(N.Rat{p2, qa2}, N.Rat{r2, sb2}, xs, ys), Laws.sse(N.Rat{p, qa}, N.Rat{r, sb}, xs, ys), sumsq(p2, N.Pos{1n+qa2}, r2, N.Pos{1n+sb2}, N.Pos{1n+lp}, l, xs, ys), N.Nat.mul_pred(N.Nat.mul_pred(N.Nat.mul_pred(lp, qa2), sb2), N.Nat.mul_pred(N.Nat.mul_pred(lp, qa2), sb2)), sumsq(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, l, xs, ys), N.Nat.mul_pred(N.Nat.mul_pred(N.Nat.mul_pred(lp, qa), sb), N.Nat.mul_pred(N.Nat.mul_pred(lp, qa), sb)), sse_den(l, lp, hl, p2, qa2, r2, sb2, xs, ys, hx, hy), sse_den(l, lp, hl, p, qa, r, sb, xs, ys, hx, hy), good)))
         : {N.Int.mul(N.Int.mul(N.Pos{1n+lp}, N.Pos{1n+lp}), w2(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), PG.rest(l, xs, ys))) == N.Pos{_} : N.Int}
       ec)),
    {==})

law ls_w2.w:
  for +l: Nat
  for +lp: Nat
  for +hl: {l == 1n+lp : Nat}
  for +p: N.Int
  for +qa: Nat
  for +r: N.Int
  for +sb: Nat
  for +p2: N.Int
  for +qa2: Nat
  for +r2: N.Int
  for +sb2: Nat
  for +xs: +List<N.Rat>
  for +ys: +List<N.Rat>
  for +hx: {PG.dvb(xs, l) == True{} : Bool}
  for +hy: {PG.dvb(ys, l) == True{} : Bool}
  for +e: {N.Int.mul(N.Int.mul(mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp}), mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp})), sumsq(p2, N.Pos{1n+qa2}, r2, N.Pos{1n+sb2}, N.Pos{1n+lp}, l, xs, ys)) == N.Int.add(N.Int.mul(N.Int.mul(mden(N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), mden(N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp})), sumsq(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, l, xs, ys)), N.Int.mul(N.Int.mul(N.Pos{1n+lp}, N.Pos{1n+lp}), w2(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), PG.rest(l, xs, ys)))) : N.Int}
  for +good: {N.Rat.is_le(Laws.sse(N.Rat{p2, qa2}, N.Rat{r2, sb2}, xs, ys), Laws.sse(N.Rat{p, qa}, N.Rat{r, sb}, xs, ys)) == True{} : Bool}
  for w: &c: Nat -> {N.Int.mul(N.Int.mul(N.Pos{1n+lp}, N.Pos{1n+lp}), w2(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), PG.rest(l, xs, ys))) == N.Pos{c} : N.Int}
  {w2(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), PG.rest(l, xs, ys)) == N.Pos{0n} : N.Int}

def ls_w2.w(l, lp, hl, p, qa, r, sb, p2, qa2, r2, sb2, xs, ys, hx, hy, e, good, w):
  match w:
    case (+c, ec):
      ls_w2.c(l, lp, hl, p, qa, r, sb, p2, qa2, r2, sb2, xs, ys, hx, hy, e, good, c, ec)

# a line at least as good leaves Σ (U x + V)² == 0
law ls_w2:
  for +l: Nat
  for +lp: Nat
  for +hl: {l == 1n+lp : Nat}
  for +p: N.Int
  for +qa: Nat
  for +r: N.Int
  for +sb: Nat
  for +p2: N.Int
  for +qa2: Nat
  for +r2: N.Int
  for +sb2: Nat
  for +xs: +List<N.Rat>
  for +ys: +List<N.Rat>
  for +hx: {PG.dvb(xs, l) == True{} : Bool}
  for +hy: {PG.dvb(ys, l) == True{} : Bool}
  for +e: {N.Int.mul(N.Int.mul(mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp}), mden(N.Pos{1n+qa}, N.Pos{1n+sb}, N.Pos{1n+lp})), sumsq(p2, N.Pos{1n+qa2}, r2, N.Pos{1n+sb2}, N.Pos{1n+lp}, l, xs, ys)) == N.Int.add(N.Int.mul(N.Int.mul(mden(N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), mden(N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp})), sumsq(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, l, xs, ys)), N.Int.mul(N.Int.mul(N.Pos{1n+lp}, N.Pos{1n+lp}), w2(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), PG.rest(l, xs, ys)))) : N.Int}
  for +good: {N.Rat.is_le(Laws.sse(N.Rat{p2, qa2}, N.Rat{r2, sb2}, xs, ys), Laws.sse(N.Rat{p, qa}, N.Rat{r, sb}, xs, ys)) == True{} : Bool}
  {w2(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), PG.rest(l, xs, ys)) == N.Pos{0n} : N.Int}

def ls_w2(l, lp, hl, p, qa, r, sb, p2, qa2, r2, sb2, xs, ys, hx, hy, e, good):
  ls_w2.w(l, lp, hl, p, qa, r, sb, p2, qa2, r2, sb2, xs, ys, hx, hy, e, good, w_pos(l, lp, hl, p, qa, r, sb, p2, qa2, r2, sb2, xs, ys, hx, hy))

law u_zero:
  for +l: Nat
  for +lp: Nat
  for +p: N.Int
  for +qa: Nat
  for +r: N.Int
  for +sb: Nat
  for +p2: N.Int
  for +qa2: Nat
  for +r2: N.Int
  for +sb2: Nat
  for +xs: +List<N.Rat>
  for +ys: +List<N.Rat>
  for +hw2: {w2(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), PG.rest(l, xs, ys)) == N.Pos{0n} : N.Int}
  for +nz: {N.Int.is_eq(PG.dexp(PG.rest(l, xs, ys)), N.Pos{0n}) == False{} : Bool}
  {uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}) == N.Pos{0n} : N.Int}

def u_zero(l, lp, p, qa, r, sb, p2, qa2, r2, sb2, xs, ys, hw2, nz):
  mul_eq_zero(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), PG.dexp(PG.rest(l, xs, ys)),
    Equal.trans(N.Int, N.Int.mul(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), PG.dexp(PG.rest(l, xs, ys))), N.Int.sub(N.Int.mul(PG.sn(PG.rest(l, xs, ys)), wx(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), PG.rest(l, xs, ys))), N.Int.mul(PG.ssx(PG.rest(l, xs, ys)), w1(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), PG.rest(l, xs, ys)))), N.Pos{0n},
      PI.IRing.eq(PI.IMul{PI.IVar{0n}, PI.IAdd{PI.IMul{PI.IVar{2n}, PI.IVar{4n}}, PI.INeg{PI.IMul{PI.IVar{3n}, PI.IVar{3n}}}}}, PI.IAdd{PI.IMul{PI.IVar{2n}, PI.IAdd{PI.IMul{PI.IVar{0n}, PI.IVar{4n}}, PI.IMul{PI.IVar{1n}, PI.IVar{3n}}}}, PI.INeg{PI.IMul{PI.IVar{3n}, PI.IAdd{PI.IMul{PI.IVar{0n}, PI.IVar{3n}}, PI.IMul{PI.IVar{1n}, PI.IVar{2n}}}}}}, [uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), PG.sn(PG.rest(l, xs, ys)), PG.ssx(PG.rest(l, xs, ys)), PG.ssxx(PG.rest(l, xs, ys))], {==}),
      (%Equal.sym(N.Int, wx(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), PG.rest(l, xs, ys)), N.Pos{0n}, wx_of_w2(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), l, L.Point.zip(xs, ys), hw2))
         : {N.Int.sub(N.Int.mul(PG.sn(PG.rest(l, xs, ys)), _), N.Int.mul(PG.ssx(PG.rest(l, xs, ys)), w1(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), PG.rest(l, xs, ys)))) == N.Pos{0n} : N.Int}
       %Equal.sym(N.Int, w1(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), PG.rest(l, xs, ys)), N.Pos{0n}, w1_of_w2(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), l, L.Point.zip(xs, ys), hw2))
         : {N.Int.sub(N.Int.mul(PG.sn(PG.rest(l, xs, ys)), N.Pos{0n}), N.Int.mul(PG.ssx(PG.rest(l, xs, ys)), _)) == N.Pos{0n} : N.Int}
       PI.IRing.eq(PI.IAdd{PI.IMul{PI.IVar{0n}, PI.IConst{N.Pos{0n}}}, PI.INeg{PI.IMul{PI.IVar{1n}, PI.IConst{N.Pos{0n}}}}}, PI.IConst{N.Pos{0n}}, [PG.sn(PG.rest(l, xs, ys)), PG.ssx(PG.rest(l, xs, ys))], {==}))),
    nz)

law v_zero:
  for +l: Nat
  for +lp: Nat
  for +p: N.Int
  for +qa: Nat
  for +r: N.Int
  for +sb: Nat
  for +p2: N.Int
  for +qa2: Nat
  for +r2: N.Int
  for +sb2: Nat
  for +xs: +List<N.Rat>
  for +ys: +List<N.Rat>
  for +hw2: {w2(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), PG.rest(l, xs, ys)) == N.Pos{0n} : N.Int}
  for +nz: {N.Int.is_eq(PG.dexp(PG.rest(l, xs, ys)), N.Pos{0n}) == False{} : Bool}
  {vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}) == N.Pos{0n} : N.Int}

def v_zero(l, lp, p, qa, r, sb, p2, qa2, r2, sb2, xs, ys, hw2, nz):
  mul_eq_zero(vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), PG.dexp(PG.rest(l, xs, ys)),
    Equal.trans(N.Int, N.Int.mul(vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), PG.dexp(PG.rest(l, xs, ys))), N.Int.sub(N.Int.mul(PG.ssxx(PG.rest(l, xs, ys)), w1(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), PG.rest(l, xs, ys))), N.Int.mul(PG.ssx(PG.rest(l, xs, ys)), wx(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), PG.rest(l, xs, ys)))), N.Pos{0n},
      PI.IRing.eq(PI.IMul{PI.IVar{1n}, PI.IAdd{PI.IMul{PI.IVar{2n}, PI.IVar{4n}}, PI.INeg{PI.IMul{PI.IVar{3n}, PI.IVar{3n}}}}}, PI.IAdd{PI.IMul{PI.IVar{4n}, PI.IAdd{PI.IMul{PI.IVar{0n}, PI.IVar{3n}}, PI.IMul{PI.IVar{1n}, PI.IVar{2n}}}}, PI.INeg{PI.IMul{PI.IVar{3n}, PI.IAdd{PI.IMul{PI.IVar{0n}, PI.IVar{4n}}, PI.IMul{PI.IVar{1n}, PI.IVar{3n}}}}}}, [uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), PG.sn(PG.rest(l, xs, ys)), PG.ssx(PG.rest(l, xs, ys)), PG.ssxx(PG.rest(l, xs, ys))], {==}),
      (%Equal.sym(N.Int, w1(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), PG.rest(l, xs, ys)), N.Pos{0n}, w1_of_w2(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), l, L.Point.zip(xs, ys), hw2))
         : {N.Int.sub(N.Int.mul(PG.ssxx(PG.rest(l, xs, ys)), _), N.Int.mul(PG.ssx(PG.rest(l, xs, ys)), wx(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), PG.rest(l, xs, ys)))) == N.Pos{0n} : N.Int}
       %Equal.sym(N.Int, wx(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), PG.rest(l, xs, ys)), N.Pos{0n}, wx_of_w2(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), l, L.Point.zip(xs, ys), hw2))
         : {N.Int.sub(N.Int.mul(PG.ssxx(PG.rest(l, xs, ys)), N.Pos{0n}), N.Int.mul(PG.ssx(PG.rest(l, xs, ys)), _)) == N.Pos{0n} : N.Int}
       PI.IRing.eq(PI.IAdd{PI.IMul{PI.IVar{0n}, PI.IConst{N.Pos{0n}}}, PI.INeg{PI.IMul{PI.IVar{1n}, PI.IConst{N.Pos{0n}}}}}, PI.IConst{N.Pos{0n}}, [PG.ssxx(PG.rest(l, xs, ys)), PG.ssx(PG.rest(l, xs, ys))], {==}))),
    nz)

# U == 0 and V == 0: the two lines are the same
law uniq_ab:
  for +l: Nat
  for +lp: Nat
  for +p: N.Int
  for +qa: Nat
  for +r: N.Int
  for +sb: Nat
  for +p2: N.Int
  for +qa2: Nat
  for +r2: N.Int
  for +sb2: Nat
  for +xs: +List<N.Rat>
  for +ys: +List<N.Rat>
  for +hw2: {w2(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), PG.rest(l, xs, ys)) == N.Pos{0n} : N.Int}
  for +nz: {N.Int.is_eq(PG.dexp(PG.rest(l, xs, ys)), N.Pos{0n}) == False{} : Bool}
  {Laws.same(N.Rat{p2, qa2}, N.Rat{p, qa}) == True{} : Bool} & {Laws.same(N.Rat{r2, sb2}, N.Rat{r, sb}) == True{} : Bool}

def uniq_ab(l, lp, p, qa, r, sb, p2, qa2, r2, sb2, xs, ys, hw2, nz):
  (PG.ieq_of(N.Int.mul(p2, N.Pos{1n+qa}), N.Int.mul(p, N.Pos{1n+qa2}),
     Equal.sym(N.Int, N.Int.mul(p, N.Pos{1n+qa2}), N.Int.mul(p2, N.Pos{1n+qa}),
       PG.sub_eq_zero(N.Int.mul(p, N.Pos{1n+qa2}), N.Int.mul(p2, N.Pos{1n+qa}),
         mul_eq_zero(N.Int.sub(N.Int.mul(p, N.Pos{1n+qa2}), N.Int.mul(p2, N.Pos{1n+qa})), N.Int.mul(N.Pos{1n+sb}, N.Pos{1n+sb2}), u_zero(l, lp, p, qa, r, sb, p2, qa2, r2, sb2, xs, ys, hw2, nz), {==})))),
   PG.ieq_of(N.Int.mul(r2, N.Pos{1n+sb}), N.Int.mul(r, N.Pos{1n+sb2}),
     Equal.sym(N.Int, N.Int.mul(r, N.Pos{1n+sb2}), N.Int.mul(r2, N.Pos{1n+sb}),
       PG.sub_eq_zero(N.Int.mul(r, N.Pos{1n+sb2}), N.Int.mul(r2, N.Pos{1n+sb}),
         mul_eq_zero(N.Int.sub(N.Int.mul(r, N.Pos{1n+sb2}), N.Int.mul(r2, N.Pos{1n+sb})), N.Int.mul(N.Pos{1n+lp}, N.Int.mul(N.Pos{1n+qa}, N.Pos{1n+qa2})), v_zero(l, lp, p, qa, r, sb, p2, qa2, r2, sb2, xs, ys, hw2, nz), {==})))))

# Through the origin (b = b2 = 0), V is 0 and Σx² != 0 pins U
law u_zero_origin:
  for +l: Nat
  for +lp: Nat
  for +p: N.Int
  for +qa: Nat
  for +p2: N.Int
  for +qa2: Nat
  for +xs: +List<N.Rat>
  for +ys: +List<N.Rat>
  for +hw2: {w2(uexp(p, N.Pos{1n+qa}, N.Pos{1n+0n}, p2, N.Pos{1n+qa2}, N.Pos{1n+0n}), vexp(N.Pos{0n}, N.Pos{1n+qa}, N.Pos{1n+0n}, N.Pos{0n}, N.Pos{1n+qa2}, N.Pos{1n+0n}, N.Pos{1n+lp}), PG.rest(l, xs, ys)) == N.Pos{0n} : N.Int}
  for +nz: {N.Int.is_eq(PG.ssxx(PG.rest(l, xs, ys)), N.Pos{0n}) == False{} : Bool}
  {Laws.same(N.Rat{p2, qa2}, N.Rat{p, qa}) == True{} : Bool}

def u_zero_origin(l, lp, p, qa, p2, qa2, xs, ys, hw2, nz):
  PG.ieq_of(N.Int.mul(p2, N.Pos{1n+qa}), N.Int.mul(p, N.Pos{1n+qa2}),
    Equal.sym(N.Int, N.Int.mul(p, N.Pos{1n+qa2}), N.Int.mul(p2, N.Pos{1n+qa}),
      PG.sub_eq_zero(N.Int.mul(p, N.Pos{1n+qa2}), N.Int.mul(p2, N.Pos{1n+qa}),
        mul_eq_zero(N.Int.sub(N.Int.mul(p, N.Pos{1n+qa2}), N.Int.mul(p2, N.Pos{1n+qa})), N.Int.mul(N.Pos{1n+0n}, N.Pos{1n+0n}),
          mul_eq_zero(uexp(p, N.Pos{1n+qa}, N.Pos{1n+0n}, p2, N.Pos{1n+qa2}, N.Pos{1n+0n}), PG.ssxx(PG.rest(l, xs, ys)),
            Equal.trans(N.Int, N.Int.mul(uexp(p, N.Pos{1n+qa}, N.Pos{1n+0n}, p2, N.Pos{1n+qa2}, N.Pos{1n+0n}), PG.ssxx(PG.rest(l, xs, ys))),
              wx(uexp(p, N.Pos{1n+qa}, N.Pos{1n+0n}, p2, N.Pos{1n+qa2}, N.Pos{1n+0n}), vexp(N.Pos{0n}, N.Pos{1n+qa}, N.Pos{1n+0n}, N.Pos{0n}, N.Pos{1n+qa2}, N.Pos{1n+0n}, N.Pos{1n+lp}), PG.rest(l, xs, ys)),
              N.Pos{0n},
              PI.IRing.eq(PI.IMul{PI.IVar{0n}, PI.IVar{5n}}, PI.IAdd{PI.IMul{PI.IVar{0n}, PI.IVar{5n}}, PI.IMul{PI.IMul{PI.IAdd{PI.IMul{PI.IConst{N.Pos{0n}}, PI.IConst{N.Pos{1n}}}, PI.INeg{PI.IMul{PI.IConst{N.Pos{0n}}, PI.IConst{N.Pos{1n}}}}}, PI.IMul{PI.IVar{1n}, PI.IMul{PI.IVar{2n}, PI.IVar{3n}}}}, PI.IVar{4n}}}, [uexp(p, N.Pos{1n+qa}, N.Pos{1n+0n}, p2, N.Pos{1n+qa2}, N.Pos{1n+0n}), N.Pos{1n+lp}, N.Pos{1n+qa}, N.Pos{1n+qa2}, PG.ssx(PG.rest(l, xs, ys)), PG.ssxx(PG.rest(l, xs, ys))], {==}),
              wx_of_w2(uexp(p, N.Pos{1n+qa}, N.Pos{1n+0n}, p2, N.Pos{1n+qa2}, N.Pos{1n+0n}), vexp(N.Pos{0n}, N.Pos{1n+qa}, N.Pos{1n+0n}, N.Pos{0n}, N.Pos{1n+qa2}, N.Pos{1n+0n}, N.Pos{1n+lp}),
                l, L.Point.zip(xs, ys), hw2)),
            nz),
          {==}))))

# The fitted line's facts
# -----------------------

law ff.s:
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +p: N.Int
  for +qa: Nat
  for +r: N.Int
  for +sb: Nat
  for +lp: Nat
  for +hl: {PZ.lv(x <> xt, y <> yt) == 1n+lp : Nat}
  for tr: Laws.Denotes(N.Rat{p, qa}, n1e(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), PG.dexp(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt))) & Laws.Denotes(N.Rat{r, sb}, n2e(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Int.mul(N.Pos{PZ.lv(x <> xt, y <> yt)}, PG.dexp(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt))))
    & {N.Int.is_eq(PG.dexp(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{0n}) == False{} : Bool}
  exs lp: Nat
  {PZ.lv(x <> xt, y <> yt) == 1n+lp : Nat}
    & {N.Int.mul(p, PG.dexp(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt))) == N.Int.mul(n1e(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{1n+qa}) : N.Int}
    & {N.Int.mul(r, N.Int.mul(N.Pos{1n+lp}, PG.dexp(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)))) == N.Int.mul(n2e(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{1n+sb}) : N.Int}
    & {N.Int.is_eq(PG.dexp(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{0n}) == False{} : Bool}

def ff.s(x, xt, y, yt, p, qa, r, sb, lp, hl, tr):
  match tr:
    case (da, (db, nz)):
      (lp, (hl, (da, ((%hl : {N.Int.mul(r, N.Int.mul(N.Pos{_}, PG.dexp(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)))) == N.Int.mul(n2e(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{1n+sb}) : N.Int}
                       db), nz))))

law ff.k:
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +p: N.Int
  for +qa: Nat
  for +r: N.Int
  for +sb: Nat
  for +ok2: {L.LinearRegression.fit.stats(True{}, PZ.lv(x <> xt, y <> yt), PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)) == Done{L.LinearRegression{True{}, N.Rat{p, qa}, N.Rat{r, sb}}} : Result<L.FitError, L.LinearRegression>}
  for +lp: Nat
  for +hl: {PZ.lv(x <> xt, y <> yt) == 1n+lp : Nat}
  exs lp: Nat
  {PZ.lv(x <> xt, y <> yt) == 1n+lp : Nat}
    & {N.Int.mul(p, PG.dexp(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt))) == N.Int.mul(n1e(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{1n+qa}) : N.Int}
    & {N.Int.mul(r, N.Int.mul(N.Pos{1n+lp}, PG.dexp(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)))) == N.Int.mul(n2e(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{1n+sb}) : N.Int}
    & {N.Int.is_eq(PG.dexp(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{0n}) == False{} : Bool}

def ff.k(x, xt, y, yt, p, qa, r, sb, ok2, lp, hl):
  ff.s(x, xt, y, yt, p, qa, r, sb, lp, hl, solve_inv(PZ.lv(x <> xt, y <> yt), PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt), N.Rat{p, qa}, N.Rat{r, sb}, ok2))

law ff.j:
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +p: N.Int
  for +qa: Nat
  for +r: N.Int
  for +sb: Nat
  for +ok2: {L.LinearRegression.fit.stats(True{}, PZ.lv(x <> xt, y <> yt), PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)) == Done{L.LinearRegression{True{}, N.Rat{p, qa}, N.Rat{r, sb}}} : Result<L.FitError, L.LinearRegression>}
  for w: PD.LeW(1n, PZ.lv(x <> xt, y <> yt))
  exs lp: Nat
  {PZ.lv(x <> xt, y <> yt) == 1n+lp : Nat}
    & {N.Int.mul(p, PG.dexp(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt))) == N.Int.mul(n1e(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{1n+qa}) : N.Int}
    & {N.Int.mul(r, N.Int.mul(N.Pos{1n+lp}, PG.dexp(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)))) == N.Int.mul(n2e(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{1n+sb}) : N.Int}
    & {N.Int.is_eq(PG.dexp(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{0n}) == False{} : Bool}

def ff.j(x, xt, y, yt, p, qa, r, sb, ok2, w):
  match w:
    case (+lp, hl):
      ff.k(x, xt, y, yt, p, qa, r, sb, ok2, lp, hl)

law ff.i:
  for +k: Nat
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +p: N.Int
  for +qa: Nat
  for +r: N.Int
  for +sb: Nat
  for inv: {List.length(&2, N.Rat, xt) == List.length(&2, N.Rat, yt) : Nat}
    & {Laws.fit_fits(k, x <> xt, y <> yt) == True{} : Bool}
    & {L.LinearRegression.fit.stats(True{}, PZ.lv(x <> xt, y <> yt), PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)) == Done{L.LinearRegression{True{}, N.Rat{p, qa}, N.Rat{r, sb}}} : Result<L.FitError, L.LinearRegression>}
  exs lp: Nat
  {PZ.lv(x <> xt, y <> yt) == 1n+lp : Nat}
    & {N.Int.mul(p, PG.dexp(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt))) == N.Int.mul(n1e(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{1n+qa}) : N.Int}
    & {N.Int.mul(r, N.Int.mul(N.Pos{1n+lp}, PG.dexp(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)))) == N.Int.mul(n2e(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{1n+sb}) : N.Int}
    & {N.Int.is_eq(PG.dexp(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{0n}) == False{} : Bool}

def ff.i(k, x, xt, y, yt, p, qa, r, sb, inv):
  match inv:
    case (len, (small, ok2)):
      ff.j(x, xt, y, yt, p, qa, r, sb, ok2, PG.lv_pos(x <> xt, y <> yt))

law ff:
  for +k: Nat
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +p: N.Int
  for +qa: Nat
  for +r: N.Int
  for +sb: Nat
  for +ok: {L.LinearRegression.fit.within(k, True{}, x <> xt, y <> yt) == Done{L.LinearRegression{True{}, N.Rat{p, qa}, N.Rat{r, sb}}} : Result<L.FitError, L.LinearRegression>}
  exs lp: Nat
  {PZ.lv(x <> xt, y <> yt) == 1n+lp : Nat}
    & {N.Int.mul(p, PG.dexp(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt))) == N.Int.mul(n1e(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{1n+qa}) : N.Int}
    & {N.Int.mul(r, N.Int.mul(N.Pos{1n+lp}, PG.dexp(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)))) == N.Int.mul(n2e(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{1n+sb}) : N.Int}
    & {N.Int.is_eq(PG.dexp(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{0n}) == False{} : Bool}

def ff(k, x, xt, y, yt, p, qa, r, sb, ok):
  ff.i(k, x, xt, y, yt, p, qa, r, sb, fit_inv(k, True{}, x, xt, y, yt, L.LinearRegression{True{}, N.Rat{p, qa}, N.Rat{r, sb}}, ok))

law ffo.s:
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +p: N.Int
  for +qa: Nat
  for +b: N.Rat
  for +lp: Nat
  for +hl: {PZ.lv(x <> xt, y <> yt) == 1n+lp : Nat}
  for tr: Laws.Denotes(N.Rat{p, qa}, PG.ssxy(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), PG.ssxx(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt))) & {b == N.Rat.zero() : N.Rat}
    & {N.Int.is_eq(PG.ssxx(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{0n}) == False{} : Bool}
  exs lp: Nat
  {PZ.lv(x <> xt, y <> yt) == 1n+lp : Nat}
    & {N.Int.mul(p, PG.ssxx(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt))) == N.Int.mul(PG.ssxy(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{1n+qa}) : N.Int}
    & {b == N.Rat.zero() : N.Rat}
    & {N.Int.is_eq(PG.ssxx(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{0n}) == False{} : Bool}

def ffo.s(x, xt, y, yt, p, qa, b, lp, hl, tr):
  match tr:
    case (da, (eb, nz)):
      (lp, (hl, (da, (eb, nz))))

law ffo.k:
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +p: N.Int
  for +qa: Nat
  for +b: N.Rat
  for +ok2: {L.LinearRegression.fit.stats(False{}, PZ.lv(x <> xt, y <> yt), PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)) == Done{L.LinearRegression{False{}, N.Rat{p, qa}, b}} : Result<L.FitError, L.LinearRegression>}
  for +lp: Nat
  for +hl: {PZ.lv(x <> xt, y <> yt) == 1n+lp : Nat}
  exs lp: Nat
  {PZ.lv(x <> xt, y <> yt) == 1n+lp : Nat}
    & {N.Int.mul(p, PG.ssxx(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt))) == N.Int.mul(PG.ssxy(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{1n+qa}) : N.Int}
    & {b == N.Rat.zero() : N.Rat}
    & {N.Int.is_eq(PG.ssxx(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{0n}) == False{} : Bool}

def ffo.k(x, xt, y, yt, p, qa, b, ok2, lp, hl):
  ffo.s(x, xt, y, yt, p, qa, b, lp, hl, solve_origin_inv(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt), N.Rat{p, qa}, b, ok2))

law ffo.j:
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +p: N.Int
  for +qa: Nat
  for +b: N.Rat
  for +ok2: {L.LinearRegression.fit.stats(False{}, PZ.lv(x <> xt, y <> yt), PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)) == Done{L.LinearRegression{False{}, N.Rat{p, qa}, b}} : Result<L.FitError, L.LinearRegression>}
  for w: PD.LeW(1n, PZ.lv(x <> xt, y <> yt))
  exs lp: Nat
  {PZ.lv(x <> xt, y <> yt) == 1n+lp : Nat}
    & {N.Int.mul(p, PG.ssxx(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt))) == N.Int.mul(PG.ssxy(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{1n+qa}) : N.Int}
    & {b == N.Rat.zero() : N.Rat}
    & {N.Int.is_eq(PG.ssxx(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{0n}) == False{} : Bool}

def ffo.j(x, xt, y, yt, p, qa, b, ok2, w):
  match w:
    case (+lp, hl):
      ffo.k(x, xt, y, yt, p, qa, b, ok2, lp, hl)

law ffo.i:
  for +k: Nat
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +p: N.Int
  for +qa: Nat
  for +b: N.Rat
  for inv: {List.length(&2, N.Rat, xt) == List.length(&2, N.Rat, yt) : Nat}
    & {Laws.fit_fits(k, x <> xt, y <> yt) == True{} : Bool}
    & {L.LinearRegression.fit.stats(False{}, PZ.lv(x <> xt, y <> yt), PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)) == Done{L.LinearRegression{False{}, N.Rat{p, qa}, b}} : Result<L.FitError, L.LinearRegression>}
  exs lp: Nat
  {PZ.lv(x <> xt, y <> yt) == 1n+lp : Nat}
    & {N.Int.mul(p, PG.ssxx(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt))) == N.Int.mul(PG.ssxy(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{1n+qa}) : N.Int}
    & {b == N.Rat.zero() : N.Rat}
    & {N.Int.is_eq(PG.ssxx(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{0n}) == False{} : Bool}

def ffo.i(k, x, xt, y, yt, p, qa, b, inv):
  match inv:
    case (len, (small, ok2)):
      ffo.j(x, xt, y, yt, p, qa, b, ok2, PG.lv_pos(x <> xt, y <> yt))

law ffo:
  for +k: Nat
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +p: N.Int
  for +qa: Nat
  for +b: N.Rat
  for +ok: {L.LinearRegression.fit.within(k, False{}, x <> xt, y <> yt) == Done{L.LinearRegression{False{}, N.Rat{p, qa}, b}} : Result<L.FitError, L.LinearRegression>}
  exs lp: Nat
  {PZ.lv(x <> xt, y <> yt) == 1n+lp : Nat}
    & {N.Int.mul(p, PG.ssxx(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt))) == N.Int.mul(PG.ssxy(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{1n+qa}) : N.Int}
    & {b == N.Rat.zero() : N.Rat}
    & {N.Int.is_eq(PG.ssxx(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{0n}) == False{} : Bool}

def ffo(k, x, xt, y, yt, p, qa, b, ok):
  ffo.i(k, x, xt, y, yt, p, qa, b, fit_inv(k, False{}, x, xt, y, yt, L.LinearRegression{False{}, N.Rat{p, qa}, b}, ok))

# least_squares
# -------------

law ls.g:
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +p: N.Int
  for +qa: Nat
  for +r: N.Int
  for +sb: Nat
  for +p2: N.Int
  for +qa2: Nat
  for +r2: N.Int
  for +sb2: Nat
  for +lp: Nat
  for +hl: {PZ.lv(x <> xt, y <> yt) == 1n+lp : Nat}
  for +ha: {N.Int.mul(p, PG.dexp(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt))) == N.Int.mul(n1e(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{1n+qa}) : N.Int}
  for +hb: {N.Int.mul(r, N.Int.mul(N.Pos{1n+lp}, PG.dexp(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)))) == N.Int.mul(n2e(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{1n+sb}) : N.Int}
  for +nz: {N.Int.is_eq(PG.dexp(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{0n}) == False{} : Bool}
  {N.Rat.is_le(Laws.sse(N.Rat{p, qa}, N.Rat{r, sb}, x <> xt, y <> yt), Laws.sse(N.Rat{p2, qa2}, N.Rat{r2, sb2}, x <> xt, y <> yt)) == True{} : Bool}

def ls.g(x, xt, y, yt, p, qa, r, sb, p2, qa2, r2, sb2, lp, hl, ha, hb, nz):
  ls_le(PZ.lv(x <> xt, y <> yt), lp, hl, p, qa, r, sb, p2, qa2, r2, sb2, x <> xt, y <> yt, PG.dvb_xs(x <> xt, y <> yt), PG.dvb_ys(x <> xt, y <> yt),
    key_zero(N.Pos{1n+lp}, p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, r2, N.Pos{1n+sb2}, PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt,
        (%Equal.sym(N.Int, rxexp(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{0n}, ne_rx(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt), ha, hb, nz))
          : {N.Int.add(N.Int.mul(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), _), N.Int.mul(vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), rexp(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)))) == N.Pos{0n} : N.Int}
        %Equal.sym(N.Int, rexp(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{0n}, ne_r(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt), ha, hb, nz))
          : {N.Int.add(N.Int.mul(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), N.Pos{0n}), N.Int.mul(vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), _)) == N.Pos{0n} : N.Int}
        PI.IRing.eq(PI.IAdd{PI.IMul{PI.IVar{0n}, PI.IConst{N.Pos{0n}}}, PI.IMul{PI.IVar{1n}, PI.IConst{N.Pos{0n}}}}, PI.IConst{N.Pos{0n}}, [uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp})], {==}))))

law ls.f:
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +p: N.Int
  for +qa: Nat
  for +r: N.Int
  for +sb: Nat
  for +p2: N.Int
  for +qa2: Nat
  for +r2: N.Int
  for +sb2: Nat
  for f: &lp: Nat -> {PZ.lv(x <> xt, y <> yt) == 1n+lp : Nat}
    & {N.Int.mul(p, PG.dexp(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt))) == N.Int.mul(n1e(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{1n+qa}) : N.Int}
    & {N.Int.mul(r, N.Int.mul(N.Pos{1n+lp}, PG.dexp(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)))) == N.Int.mul(n2e(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{1n+sb}) : N.Int}
    & {N.Int.is_eq(PG.dexp(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{0n}) == False{} : Bool}
  {N.Rat.is_le(Laws.sse(N.Rat{p, qa}, N.Rat{r, sb}, x <> xt, y <> yt), Laws.sse(N.Rat{p2, qa2}, N.Rat{r2, sb2}, x <> xt, y <> yt)) == True{} : Bool}

def ls.f(x, xt, y, yt, p, qa, r, sb, p2, qa2, r2, sb2, f):
  match f:
    case (+lp, (hl, (ha, (hb, nz)))):
      ls.g(x, xt, y, yt, p, qa, r, sb, p2, qa2, r2, sb2, lp, hl, ha, hb, nz)

law least_squares:
  for +k: Nat
  for xs: +List<N.Rat>
  for ys: +List<N.Rat>
  for a: N.Rat
  for b: N.Rat
  for +ok: {L.LinearRegression.fit.within(k, True{}, xs, ys) == Done{L.LinearRegression{True{}, a, b}} : Result<L.FitError, L.LinearRegression>}
  for a2: N.Rat
  for b2: N.Rat
  {N.Rat.is_le(Laws.sse(a, b, xs, ys), Laws.sse(a2, b2, xs, ys)) == True{} : Bool}

def least_squares(k, xs, ys, a, b, ok, a2, b2):
  match xs ys:
    case Nil{} _:
      {==}
    case Con{x, xt} Nil{}:
      {==}
    case Con{+x, +xt} Con{+y, +yt}:
      match a b a2 b2:
        case N.Rat{+p, +qa} N.Rat{+r, +sb} N.Rat{+p2, +qa2} N.Rat{+r2, +sb2}:
          ls.f(x, xt, y, yt, p, qa, r, sb, p2, qa2, r2, sb2, ff(k, x, xt, y, yt, p, qa, r, sb, ok))

law lsu.g:
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +p: N.Int
  for +qa: Nat
  for +r: N.Int
  for +sb: Nat
  for +p2: N.Int
  for +qa2: Nat
  for +r2: N.Int
  for +sb2: Nat
  for +lp: Nat
  for +hl: {PZ.lv(x <> xt, y <> yt) == 1n+lp : Nat}
  for +ha: {N.Int.mul(p, PG.dexp(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt))) == N.Int.mul(n1e(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{1n+qa}) : N.Int}
  for +hb: {N.Int.mul(r, N.Int.mul(N.Pos{1n+lp}, PG.dexp(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)))) == N.Int.mul(n2e(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{1n+sb}) : N.Int}
  for +nz: {N.Int.is_eq(PG.dexp(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{0n}) == False{} : Bool}
  for +good: {N.Rat.is_le(Laws.sse(N.Rat{p2, qa2}, N.Rat{r2, sb2}, x <> xt, y <> yt), Laws.sse(N.Rat{p, qa}, N.Rat{r, sb}, x <> xt, y <> yt)) == True{} : Bool}
  {Laws.same(N.Rat{p2, qa2}, N.Rat{p, qa}) == True{} : Bool} & {Laws.same(N.Rat{r2, sb2}, N.Rat{r, sb}) == True{} : Bool}

def lsu.g(x, xt, y, yt, p, qa, r, sb, p2, qa2, r2, sb2, lp, hl, ha, hb, nz, good):
  uniq_ab(PZ.lv(x <> xt, y <> yt), lp, p, qa, r, sb, p2, qa2, r2, sb2, x <> xt, y <> yt,
    ls_w2(PZ.lv(x <> xt, y <> yt), lp, hl, p, qa, r, sb, p2, qa2, r2, sb2, x <> xt, y <> yt, PG.dvb_xs(x <> xt, y <> yt), PG.dvb_ys(x <> xt, y <> yt),
      key_zero(N.Pos{1n+lp}, p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, r2, N.Pos{1n+sb2}, PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt,
        (%Equal.sym(N.Int, rxexp(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{0n}, ne_rx(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt), ha, hb, nz))
          : {N.Int.add(N.Int.mul(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), _), N.Int.mul(vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), rexp(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)))) == N.Pos{0n} : N.Int}
        %Equal.sym(N.Int, rexp(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{0n}, ne_r(p, N.Pos{1n+qa}, r, N.Pos{1n+sb}, N.Pos{1n+lp}, PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt), ha, hb, nz))
          : {N.Int.add(N.Int.mul(uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), N.Pos{0n}), N.Int.mul(vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp}), _)) == N.Pos{0n} : N.Int}
        PI.IRing.eq(PI.IAdd{PI.IMul{PI.IVar{0n}, PI.IConst{N.Pos{0n}}}, PI.IMul{PI.IVar{1n}, PI.IConst{N.Pos{0n}}}}, PI.IConst{N.Pos{0n}}, [uexp(p, N.Pos{1n+qa}, N.Pos{1n+sb}, p2, N.Pos{1n+qa2}, N.Pos{1n+sb2}), vexp(r, N.Pos{1n+qa}, N.Pos{1n+sb}, r2, N.Pos{1n+qa2}, N.Pos{1n+sb2}, N.Pos{1n+lp})], {==}))),
      good),
    nz)

law lsu.f:
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +p: N.Int
  for +qa: Nat
  for +r: N.Int
  for +sb: Nat
  for +p2: N.Int
  for +qa2: Nat
  for +r2: N.Int
  for +sb2: Nat
  for f: &lp: Nat -> {PZ.lv(x <> xt, y <> yt) == 1n+lp : Nat}
    & {N.Int.mul(p, PG.dexp(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt))) == N.Int.mul(n1e(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{1n+qa}) : N.Int}
    & {N.Int.mul(r, N.Int.mul(N.Pos{1n+lp}, PG.dexp(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)))) == N.Int.mul(n2e(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{1n+sb}) : N.Int}
    & {N.Int.is_eq(PG.dexp(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{0n}) == False{} : Bool}
  for +good: {N.Rat.is_le(Laws.sse(N.Rat{p2, qa2}, N.Rat{r2, sb2}, x <> xt, y <> yt), Laws.sse(N.Rat{p, qa}, N.Rat{r, sb}, x <> xt, y <> yt)) == True{} : Bool}
  {Laws.same(N.Rat{p2, qa2}, N.Rat{p, qa}) == True{} : Bool} & {Laws.same(N.Rat{r2, sb2}, N.Rat{r, sb}) == True{} : Bool}

def lsu.f(x, xt, y, yt, p, qa, r, sb, p2, qa2, r2, sb2, f, good):
  match f:
    case (+lp, (hl, (ha, (hb, nz)))):
      lsu.g(x, xt, y, yt, p, qa, r, sb, p2, qa2, r2, sb2, lp, hl, ha, hb, nz, good)

law least_squares_unique:
  for +k: Nat
  for xs: +List<N.Rat>
  for ys: +List<N.Rat>
  for a: N.Rat
  for b: N.Rat
  for +ok: {L.LinearRegression.fit.within(k, True{}, xs, ys) == Done{L.LinearRegression{True{}, a, b}} : Result<L.FitError, L.LinearRegression>}
  for a2: N.Rat
  for b2: N.Rat
  for +good: {N.Rat.is_le(Laws.sse(a2, b2, xs, ys), Laws.sse(a, b, xs, ys)) == True{} : Bool}
  {Laws.same(a2, a) == True{} : Bool} & {Laws.same(b2, b) == True{} : Bool}

def least_squares_unique(k, xs, ys, a, b, ok, a2, b2, good):
  match xs ys:
    case Nil{} Nil{}:
      Empty.absurd({Laws.same(a2, a) == True{} : Bool} & {Laws.same(b2, b) == True{} : Bool},
        fail_ne_done(L.Empty{}, L.LinearRegression{True{}, a, b}, ok))
    case Nil{} Con{y, yt}:
      Empty.absurd({Laws.same(a2, a) == True{} : Bool} & {Laws.same(b2, b) == True{} : Bool},
        fail_ne_done(L.LengthMismatch{}, L.LinearRegression{True{}, a, b}, ok))
    case Con{x, xt} Nil{}:
      Empty.absurd({Laws.same(a2, a) == True{} : Bool} & {Laws.same(b2, b) == True{} : Bool},
        fail_ne_done(L.LengthMismatch{}, L.LinearRegression{True{}, a, b}, ok))
    case Con{+x, +xt} Con{+y, +yt}:
      match a b a2 b2:
        case N.Rat{+p, +qa} N.Rat{+r, +sb} N.Rat{+p2, +qa2} N.Rat{+r2, +sb2}:
          lsu.f(x, xt, y, yt, p, qa, r, sb, p2, qa2, r2, sb2, ff(k, x, xt, y, yt, p, qa, r, sb, ok), good)

law lso.g:
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +p: N.Int
  for +qa: Nat
  for +b: N.Rat
  for +p2: N.Int
  for +qa2: Nat
  for +lp: Nat
  for +hl: {PZ.lv(x <> xt, y <> yt) == 1n+lp : Nat}
  for +ha: {N.Int.mul(p, PG.ssxx(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt))) == N.Int.mul(PG.ssxy(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{1n+qa}) : N.Int}
  for +eb: {b == N.Rat.zero() : N.Rat}
  for +nz: {N.Int.is_eq(PG.ssxx(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{0n}) == False{} : Bool}
  {N.Rat.is_le(Laws.sse(N.Rat{p, qa}, b, x <> xt, y <> yt), Laws.sse(N.Rat{p2, qa2}, N.Rat.zero(), x <> xt, y <> yt)) == True{} : Bool}

def lso.g(x, xt, y, yt, p, qa, b, p2, qa2, lp, hl, ha, eb, nz):
  %Equal.sym(N.Rat, b, N.Rat.zero(), eb) : {N.Rat.is_le(Laws.sse(N.Rat{p, qa}, _, x <> xt, y <> yt), Laws.sse(N.Rat{p2, qa2}, N.Rat.zero(), x <> xt, y <> yt)) == True{} : Bool}
  ls_le(PZ.lv(x <> xt, y <> yt), lp, hl, p, qa, N.Pos{0n}, 0n, p2, qa2, N.Pos{0n}, 0n, x <> xt, y <> yt, PG.dvb_xs(x <> xt, y <> yt), PG.dvb_ys(x <> xt, y <> yt),
    key_zero(N.Pos{1n+lp}, p, N.Pos{1n+qa}, N.Pos{0n}, N.Pos{1n+0n}, p2, N.Pos{1n+qa2}, N.Pos{0n}, N.Pos{1n+0n}, PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt,
        (%Equal.sym(N.Int, rxexp(p, N.Pos{1n+qa}, N.Pos{0n}, N.Pos{1n+0n}, N.Pos{1n+lp}, PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{0n}, ne_rx_origin(p, N.Pos{1n+qa}, N.Pos{1n+lp}, PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt), ha, nz))
          : {N.Int.add(N.Int.mul(uexp(p, N.Pos{1n+qa}, N.Pos{1n+0n}, p2, N.Pos{1n+qa2}, N.Pos{1n+0n}), _), N.Int.mul(vexp(N.Pos{0n}, N.Pos{1n+qa}, N.Pos{1n+0n}, N.Pos{0n}, N.Pos{1n+qa2}, N.Pos{1n+0n}, N.Pos{1n+lp}), rexp(p, N.Pos{1n+qa}, N.Pos{0n}, N.Pos{1n+0n}, N.Pos{1n+lp}, PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)))) == N.Pos{0n} : N.Int}
        PI.IRing.eq(PI.IAdd{PI.IMul{PI.IVar{0n}, PI.IConst{N.Pos{0n}}}, PI.IMul{PI.IMul{PI.IAdd{PI.IMul{PI.IConst{N.Pos{0n}}, PI.IConst{N.Pos{1n}}}, PI.INeg{PI.IMul{PI.IConst{N.Pos{0n}}, PI.IConst{N.Pos{1n}}}}}, PI.IMul{PI.IVar{1n}, PI.IMul{PI.IVar{2n}, PI.IVar{3n}}}}, PI.IVar{4n}}}, PI.IConst{N.Pos{0n}}, [uexp(p, N.Pos{1n+qa}, N.Pos{1n+0n}, p2, N.Pos{1n+qa2}, N.Pos{1n+0n}), N.Pos{1n+lp}, N.Pos{1n+qa}, N.Pos{1n+qa2}, rexp(p, N.Pos{1n+qa}, N.Pos{0n}, N.Pos{1n+0n}, N.Pos{1n+lp}, PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt))], {==}))))

law lso.f:
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +p: N.Int
  for +qa: Nat
  for +b: N.Rat
  for +p2: N.Int
  for +qa2: Nat
  for f: &lp: Nat -> {PZ.lv(x <> xt, y <> yt) == 1n+lp : Nat}
    & {N.Int.mul(p, PG.ssxx(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt))) == N.Int.mul(PG.ssxy(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{1n+qa}) : N.Int}
    & {b == N.Rat.zero() : N.Rat}
    & {N.Int.is_eq(PG.ssxx(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{0n}) == False{} : Bool}
  {N.Rat.is_le(Laws.sse(N.Rat{p, qa}, b, x <> xt, y <> yt), Laws.sse(N.Rat{p2, qa2}, N.Rat.zero(), x <> xt, y <> yt)) == True{} : Bool}

def lso.f(x, xt, y, yt, p, qa, b, p2, qa2, f):
  match f:
    case (+lp, (hl, (ha, (eb, nz)))):
      lso.g(x, xt, y, yt, p, qa, b, p2, qa2, lp, hl, ha, eb, nz)

law least_squares_origin:
  for +k: Nat
  for xs: +List<N.Rat>
  for ys: +List<N.Rat>
  for a: N.Rat
  for +b: N.Rat
  for +ok: {L.LinearRegression.fit.within(k, False{}, xs, ys) == Done{L.LinearRegression{False{}, a, b}} : Result<L.FitError, L.LinearRegression>}
  for a2: N.Rat
  {N.Rat.is_le(Laws.sse(a, b, xs, ys), Laws.sse(a2, N.Rat.zero(), xs, ys)) == True{} : Bool}

def least_squares_origin(k, xs, ys, a, b, ok, a2):
  match xs ys:
    case Nil{} _:
      {==}
    case Con{x, xt} Nil{}:
      {==}
    case Con{+x, +xt} Con{+y, +yt}:
      match a a2:
        case N.Rat{+p, +qa} N.Rat{+p2, +qa2}:
          lso.f(x, xt, y, yt, p, qa, b, p2, qa2, ffo(k, x, xt, y, yt, p, qa, b, ok))

law lsou.g:
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +p: N.Int
  for +qa: Nat
  for +b: N.Rat
  for +p2: N.Int
  for +qa2: Nat
  for +lp: Nat
  for +hl: {PZ.lv(x <> xt, y <> yt) == 1n+lp : Nat}
  for +ha: {N.Int.mul(p, PG.ssxx(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt))) == N.Int.mul(PG.ssxy(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{1n+qa}) : N.Int}
  for +eb: {b == N.Rat.zero() : N.Rat}
  for +nz: {N.Int.is_eq(PG.ssxx(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{0n}) == False{} : Bool}
  for +good: {N.Rat.is_le(Laws.sse(N.Rat{p2, qa2}, N.Rat.zero(), x <> xt, y <> yt), Laws.sse(N.Rat{p, qa}, b, x <> xt, y <> yt)) == True{} : Bool}
  {Laws.same(N.Rat{p2, qa2}, N.Rat{p, qa}) == True{} : Bool}

def lsou.g(x, xt, y, yt, p, qa, b, p2, qa2, lp, hl, ha, eb, nz, good):
  u_zero_origin(PZ.lv(x <> xt, y <> yt), lp, p, qa, p2, qa2, x <> xt, y <> yt,
    ls_w2(PZ.lv(x <> xt, y <> yt), lp, hl, p, qa, N.Pos{0n}, 0n, p2, qa2, N.Pos{0n}, 0n, x <> xt, y <> yt, PG.dvb_xs(x <> xt, y <> yt), PG.dvb_ys(x <> xt, y <> yt),
      key_zero(N.Pos{1n+lp}, p, N.Pos{1n+qa}, N.Pos{0n}, N.Pos{1n+0n}, p2, N.Pos{1n+qa2}, N.Pos{0n}, N.Pos{1n+0n}, PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt,
        (%Equal.sym(N.Int, rxexp(p, N.Pos{1n+qa}, N.Pos{0n}, N.Pos{1n+0n}, N.Pos{1n+lp}, PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{0n}, ne_rx_origin(p, N.Pos{1n+qa}, N.Pos{1n+lp}, PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt), ha, nz))
          : {N.Int.add(N.Int.mul(uexp(p, N.Pos{1n+qa}, N.Pos{1n+0n}, p2, N.Pos{1n+qa2}, N.Pos{1n+0n}), _), N.Int.mul(vexp(N.Pos{0n}, N.Pos{1n+qa}, N.Pos{1n+0n}, N.Pos{0n}, N.Pos{1n+qa2}, N.Pos{1n+0n}, N.Pos{1n+lp}), rexp(p, N.Pos{1n+qa}, N.Pos{0n}, N.Pos{1n+0n}, N.Pos{1n+lp}, PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)))) == N.Pos{0n} : N.Int}
        PI.IRing.eq(PI.IAdd{PI.IMul{PI.IVar{0n}, PI.IConst{N.Pos{0n}}}, PI.IMul{PI.IMul{PI.IAdd{PI.IMul{PI.IConst{N.Pos{0n}}, PI.IConst{N.Pos{1n}}}, PI.INeg{PI.IMul{PI.IConst{N.Pos{0n}}, PI.IConst{N.Pos{1n}}}}}, PI.IMul{PI.IVar{1n}, PI.IMul{PI.IVar{2n}, PI.IVar{3n}}}}, PI.IVar{4n}}}, PI.IConst{N.Pos{0n}}, [uexp(p, N.Pos{1n+qa}, N.Pos{1n+0n}, p2, N.Pos{1n+qa2}, N.Pos{1n+0n}), N.Pos{1n+lp}, N.Pos{1n+qa}, N.Pos{1n+qa2}, rexp(p, N.Pos{1n+qa}, N.Pos{0n}, N.Pos{1n+0n}, N.Pos{1n+lp}, PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt))], {==}))),
      (%eb : {N.Rat.is_le(Laws.sse(N.Rat{p2, qa2}, N.Rat.zero(), x <> xt, y <> yt), Laws.sse(N.Rat{p, qa}, _, x <> xt, y <> yt)) == True{} : Bool}
       good)),
    nz)

law lsou.f:
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +p: N.Int
  for +qa: Nat
  for +b: N.Rat
  for +p2: N.Int
  for +qa2: Nat
  for f: &lp: Nat -> {PZ.lv(x <> xt, y <> yt) == 1n+lp : Nat}
    & {N.Int.mul(p, PG.ssxx(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt))) == N.Int.mul(PG.ssxy(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{1n+qa}) : N.Int}
    & {b == N.Rat.zero() : N.Rat}
    & {N.Int.is_eq(PG.ssxx(PG.rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), N.Pos{0n}) == False{} : Bool}
  for +good: {N.Rat.is_le(Laws.sse(N.Rat{p2, qa2}, N.Rat.zero(), x <> xt, y <> yt), Laws.sse(N.Rat{p, qa}, b, x <> xt, y <> yt)) == True{} : Bool}
  {Laws.same(N.Rat{p2, qa2}, N.Rat{p, qa}) == True{} : Bool}

def lsou.f(x, xt, y, yt, p, qa, b, p2, qa2, f, good):
  match f:
    case (+lp, (hl, (ha, (eb, nz)))):
      lsou.g(x, xt, y, yt, p, qa, b, p2, qa2, lp, hl, ha, eb, nz, good)

law least_squares_origin_unique:
  for +k: Nat
  for xs: +List<N.Rat>
  for ys: +List<N.Rat>
  for a: N.Rat
  for +b: N.Rat
  for +ok: {L.LinearRegression.fit.within(k, False{}, xs, ys) == Done{L.LinearRegression{False{}, a, b}} : Result<L.FitError, L.LinearRegression>}
  for a2: N.Rat
  for +good: {N.Rat.is_le(Laws.sse(a2, N.Rat.zero(), xs, ys), Laws.sse(a, b, xs, ys)) == True{} : Bool}
  {Laws.same(a2, a) == True{} : Bool}

def least_squares_origin_unique(k, xs, ys, a, b, ok, a2, good):
  match xs ys:
    case Nil{} Nil{}:
      Empty.absurd({Laws.same(a2, a) == True{} : Bool}, fail_ne_done(L.Empty{}, L.LinearRegression{False{}, a, b}, ok))
    case Nil{} Con{y, yt}:
      Empty.absurd({Laws.same(a2, a) == True{} : Bool}, fail_ne_done(L.LengthMismatch{}, L.LinearRegression{False{}, a, b}, ok))
    case Con{x, xt} Nil{}:
      Empty.absurd({Laws.same(a2, a) == True{} : Bool}, fail_ne_done(L.LengthMismatch{}, L.LinearRegression{False{}, a, b}, ok))
    case Con{+x, +xt} Con{+y, +yt}:
      match a a2:
        case N.Rat{+p, +qa} N.Rat{+p2, +qa2}:
          lsou.f(x, xt, y, yt, p, qa, b, p2, qa2, ffo(k, x, xt, y, yt, p, qa, b, ok), good)
