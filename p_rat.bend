import Base
import ./num.bend as N
import ./p_nat.bend as PN
import ./p_ring.bend as R
import ./p_int.bend as PI
import ./p_div.bend as PD
import ./LAWS.bend as L

# Rat: reduce gives lowest terms with the right value, and lowest terms
# are unique.

# num, den, Canon and Denotes are the ones LAWS.bend defines.

# Int helpers
# -----------

def Int.isp(z: N.Int) -> Type:
  match z:
    case N.Pos{n}:
      Unit
    case N.Neg{n}:
      Empty

law pos_ne_neg:
  for +m: Nat
  for +n: Nat
  for e: {N.Pos{m} == N.Neg{n} : N.Int}
  Empty

def pos_ne_neg(m, n, e):
  %e : Int.isp(_)
  Unit{}

def Int.negv(z: N.Int) -> Nat:
  match z:
    case N.Pos{n}:
      0n
    case N.Neg{n}:
      n

law pos_inj:
  for +m: Nat
  for +n: Nat
  for e: {N.Pos{m} == N.Pos{n} : N.Int}
  {m == n : Nat}

def pos_inj(m, n, e):
  Equal.cong(N.Int, Nat, z => PI.Int.pp(z), N.Pos{m}, N.Pos{n}, e)

law neg_inj:
  for +m: Nat
  for +n: Nat
  for e: {N.Neg{m} == N.Neg{n} : N.Int}
  {m == n : Nat}

def neg_inj(m, n, e):
  Equal.cong(N.Int, Nat, z => Int.negv(z), N.Neg{m}, N.Neg{n}, e)

law abs_minus:
  for +x: Nat
  {N.Int.abs(N.Int.minus(x)) == x : Nat}

def abs_minus(x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

law abs_neg:
  for +z: N.Int
  {N.Int.abs(N.Int.neg(z)) == N.Int.abs(z) : Nat}

def abs_neg(z):
  match z:
    case N.Pos{n}:
      abs_minus(n)
    case N.Neg{n}:
      {==}

law abs_mul_pos:
  for +x: N.Int
  for +c: Nat
  {N.Int.abs(N.Int.mul(x, N.Pos{c})) == Nat.mul(N.Int.abs(x), c) : Nat}

def abs_mul_pos(x, c):
  match x:
    case N.Pos{m}:
      {==}
    case N.Neg{m}:
      abs_minus(Nat.mul(1n+m, c))

law mul_minus_pos:
  for +x: Nat
  for +y: Nat
  {N.Int.mul(N.Int.minus(x), N.Pos{y}) == N.Int.minus(Nat.mul(x, y)) : N.Int}

def mul_minus_pos(x, y):
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

# x (1 + c) == y (1 + c) gives x == y.
law int_cancel:
  for +x: N.Int
  for +y: N.Int
  for +c: Nat
  for e: {N.Int.mul(x, N.Pos{1n+c}) == N.Int.mul(y, N.Pos{1n+c}) : N.Int}
  {x == y : N.Int}

def int_cancel(x, y, c, e):
  match x y:
    case N.Pos{m} N.Pos{n}:
      %PD.mul_cancel_r(c, m, n, pos_inj(Nat.mul(m, 1n+c), Nat.mul(n, 1n+c), e)) : {N.Pos{m} == N.Pos{_} : N.Int}
      {==}
    case N.Pos{m} N.Neg{n}:
      Empty.absurd({N.Pos{m} == N.Neg{n} : N.Int}, pos_ne_neg(Nat.mul(m, 1n+c), Nat.add(c, Nat.mul(n, 1n+c)), e))
    case N.Neg{m} N.Pos{n}:
      Empty.absurd({N.Neg{m} == N.Pos{n} : N.Int},
        pos_ne_neg(Nat.mul(n, 1n+c), Nat.add(c, Nat.mul(m, 1n+c)),
          Equal.sym(N.Int, N.Neg{Nat.add(c, Nat.mul(m, 1n+c))}, N.Pos{Nat.mul(n, 1n+c)}, e)))
    case N.Neg{m} N.Neg{n}:
      %PD.mul_cancel_r(c, m, n,
          PD.add_left_cancel(c, Nat.mul(m, 1n+c), Nat.mul(n, 1n+c),
            neg_inj(Nat.add(c, Nat.mul(m, 1n+c)), Nat.add(c, Nat.mul(n, 1n+c)), e)))
        : {N.Neg{m} == N.Neg{_} : N.Int}
      {==}

# reduce
# ------

# m == g qa gives m / g == qa.
law div_of:
  for +m: Nat
  for +gp: Nat
  for +qa: Nat
  for e: {m == Nat.mul(1n+gp, qa) : Nat}
  {Nat.div(m, 1n+gp) == qa : Nat}

def div_of(m, gp, qa, e):
  %Equal.sym(Nat, m, Nat.mul(1n+gp, qa), e) : {Nat.div(_, 1n+gp) == qa : Nat}
  %Equal.sym(Nat, Nat.mul(1n+gp, qa), Nat.mul(qa, 1n+gp), PN.mul_comm(1n+gp, qa)) : {Nat.div(_, 1n+gp) == qa : Nat}
  PD.div_exact(qa, gp)

law abs_divnat:
  for +n: N.Int
  for +gp: Nat
  for +qa: Nat
  for e: {N.Int.abs(n) == Nat.mul(1n+gp, qa) : Nat}
  {N.Int.abs(N.Int.div_nat(n, 1n+gp)) == qa : Nat}

def abs_divnat(n, gp, qa, e):
  match n:
    case N.Pos{m}:
      div_of(m, gp, qa, e)
    case N.Neg{m}:
      %Equal.sym(Nat, N.Int.abs(N.Int.minus(Nat.div(1n+m, 1n+gp))), Nat.div(1n+m, 1n+gp), abs_minus(Nat.div(1n+m, 1n+gp)))
        : {_ == qa : Nat}
      div_of(1n+m, gp, qa, e)

# (n / g) (g c) == n c, when g divides |n|.
law mul_divnat:
  for +n: N.Int
  for +gp: Nat
  for +qa: Nat
  for +e: {N.Int.abs(n) == Nat.mul(1n+gp, qa) : Nat}
  for +c: Nat
  {N.Int.mul(N.Int.div_nat(n, 1n+gp), N.Pos{Nat.mul(1n+gp, c)}) == N.Int.mul(n, N.Pos{c}) : N.Int}

def mul_divnat(n, gp, qa, e, c):
  match n:
    case N.Pos{m}:
      %Equal.sym(Nat, Nat.div(m, 1n+gp), qa, div_of(m, gp, qa, e))
        : {N.Pos{Nat.mul(_, Nat.mul(1n+gp, c))} == N.Pos{Nat.mul(m, c)} : N.Int}
      %Equal.sym(Nat, m, Nat.mul(1n+gp, qa), e)
        : {N.Pos{Nat.mul(qa, Nat.mul(1n+gp, c))} == N.Pos{Nat.mul(_, c)} : N.Int}
      %R.Ring.eq(
          R.EMul{R.EVar{0n}, R.EMul{R.EAdd{R.ENum{1n}, R.EVar{1n}}, R.EVar{2n}}},
          R.EMul{R.EMul{R.EAdd{R.ENum{1n}, R.EVar{1n}}, R.EVar{0n}}, R.EVar{2n}},
          [qa, gp, c], {==})
        : {N.Pos{Nat.mul(qa, Nat.mul(1n+gp, c))} == N.Pos{_} : N.Int}
      {==}
    case N.Neg{m}:
      %Equal.sym(N.Int, N.Int.mul(N.Int.minus(Nat.div(1n+m, 1n+gp)), N.Pos{Nat.mul(1n+gp, c)}),
          N.Int.minus(Nat.mul(Nat.div(1n+m, 1n+gp), Nat.mul(1n+gp, c))),
          mul_minus_pos(Nat.div(1n+m, 1n+gp), Nat.mul(1n+gp, c)))
        : {_ == N.Int.minus(Nat.mul(1n+m, c)) : N.Int}
      %Equal.sym(Nat, Nat.div(1n+m, 1n+gp), qa, div_of(1n+m, gp, qa, e))
        : {N.Int.minus(Nat.mul(_, Nat.mul(1n+gp, c))) == N.Int.minus(Nat.mul(1n+m, c)) : N.Int}
      %Equal.sym(Nat, 1n+m, Nat.mul(1n+gp, qa), e)
        : {N.Int.minus(Nat.mul(qa, Nat.mul(1n+gp, c))) == N.Int.minus(Nat.mul(_, c)) : N.Int}
      %R.Ring.eq(
          R.EMul{R.EVar{0n}, R.EMul{R.EAdd{R.ENum{1n}, R.EVar{1n}}, R.EVar{2n}}},
          R.EMul{R.EMul{R.EAdd{R.ENum{1n}, R.EVar{1n}}, R.EVar{0n}}, R.EVar{2n}},
          [qa, gp, c], {==})
        : {N.Int.minus(Nat.mul(qa, Nat.mul(1n+gp, c))) == N.Int.minus(_) : N.Int}
      {==}

law red.canon.fin:
  for +gp: Nat
  for +k: Nat
  for +u: Nat
  for eu: {1n+gp == Nat.mul(Nat.mul(1n+gp, k), u) : Nat}
  {k == 1n : Nat}

def red.canon.fin(gp, k, u, eu):
  PD.mul_eq_one(k, u, PD.mul_cancel_r(gp, Nat.mul(k, u), 1n,
    (%Equal.sym(Nat, Nat.add(1n+gp, 0n), 1n+gp, PN.add_zero_r(1n+gp)) : {Nat.mul(Nat.mul(k, u), 1n+gp) == _ : Nat}
     %Equal.sym(Nat, 1n+gp, Nat.mul(Nat.mul(1n+gp, k), u), eu) : {Nat.mul(Nat.mul(k, u), 1n+gp) == _ : Nat}
     R.Ring.eq(
       R.EMul{R.EMul{R.EVar{0n}, R.EVar{1n}}, R.EAdd{R.ENum{1n}, R.EVar{2n}}},
       R.EMul{R.EMul{R.EAdd{R.ENum{1n}, R.EVar{2n}}, R.EVar{0n}}, R.EVar{1n}},
       [k, u, gp], {==}))))

law red.canon.dv:
  for +gp: Nat
  for +k: Nat
  for +a: Nat
  for +s: Nat
  for es: {a == Nat.mul(k, s) : Nat}
  PD.Dv(Nat.mul(1n+gp, k), Nat.mul(1n+gp, a))

def red.canon.dv(gp, k, a, s, es):
  (s, (%Equal.sym(Nat, a, Nat.mul(k, s), es) : {Nat.mul(1n+gp, _) == Nat.mul(Nat.mul(1n+gp, k), s) : Nat}
       Equal.sym(Nat, Nat.mul(Nat.mul(1n+gp, k), s), Nat.mul(1n+gp, Nat.mul(k, s)), PN.mul_assoc(1n+gp, k, s))))

law red.canon.end:
  for +gp: Nat
  for +k: Nat
  for dg: PD.Dv(Nat.mul(1n+gp, k), 1n+gp)
  {k == 1n : Nat}

def red.canon.end(gp, k, dg):
  match dg:
    case (u, eu):
      red.canon.fin(gp, k, u, eu)

# The lowest-terms half of reduce: any common divisor of |n| / g and d / g
# is 1, because g times it divides g.
law red.canon:
  for +gp: Nat
  for +qa: Nat
  for +qdp: Nat
  for great: @k: Nat -> PD.Dv(k, Nat.mul(1n+gp, qa)) -> PD.Dv(k, Nat.mul(1n+gp, 1n+qdp)) -> PD.Dv(k, 1n+gp)
  for +k: Nat
  for d1: PD.Dv(k, qa)
  for d2: PD.Dv(k, 1n+qdp)
  {k == 1n : Nat}

def red.canon(gp, qa, qdp, great, k, d1, d2):
  match d1:
    case (s, es):
      match d2:
        case (t, et):
          red.canon.end(gp, k,
            great(Nat.mul(1n+gp, k), red.canon.dv(gp, k, qa, s, es), red.canon.dv(gp, k, 1n+qdp, t, et)))

law red.den:
  for +dp: Nat
  for +gp: Nat
  for +qdp: Nat
  for ed: {1n+dp == Nat.mul(1n+gp, 1n+qdp) : Nat}
  {Nat.sub(Nat.div(1n+dp, 1n+gp), 1n) == qdp : Nat}

def red.den(dp, gp, qdp, ed):
  %Equal.sym(Nat, Nat.div(1n+dp, 1n+gp), 1n+qdp, div_of(1n+dp, gp, 1n+qdp, ed)) : {Nat.sub(_, 1n) == qdp : Nat}
  PI.Nat.sub_zero_r(qdp)

law red.go2:
  for +n: N.Int
  for +dp: Nat
  for +gp: Nat
  for +qa: Nat
  for +ea: {N.Int.abs(n) == Nat.mul(1n+gp, qa) : Nat}
  for +qdp: Nat
  for +ed: {1n+dp == Nat.mul(1n+gp, 1n+qdp) : Nat}
  for great: @k: Nat -> PD.Dv(k, N.Int.abs(n)) -> PD.Dv(k, 1n+dp) -> PD.Dv(k, 1n+gp)
  L.Canon(N.Rat.reduce.go(n, 1n+dp, 1n+gp)) & L.Denotes(N.Rat.reduce.go(n, 1n+dp, 1n+gp), n, N.Pos{1n+dp})

def red.go2(n, dp, gp, qa, ea, qdp, ed, great):
  %Equal.sym(Nat, Nat.sub(Nat.div(1n+dp, 1n+gp), 1n), qdp, red.den(dp, gp, qdp, ed))
    : L.Canon(N.Rat{N.Int.div_nat(n, 1n+gp), _}) & L.Denotes(N.Rat{N.Int.div_nat(n, 1n+gp), _}, n, N.Pos{1n+dp})
  (+k => d1 => d2 =>
     red.canon(gp, qa, qdp,
       +j => e1 => e2 =>
         great(j,
           (%Equal.sym(Nat, N.Int.abs(n), Nat.mul(1n+gp, qa), ea) : PD.Dv(j, _)
            e1),
           (%Equal.sym(Nat, 1n+dp, Nat.mul(1n+gp, 1n+qdp), ed) : PD.Dv(j, _)
            e2)),
       k,
       (%abs_divnat(n, gp, qa, ea) : PD.Dv(k, _)
        d1),
       d2),
   (%Equal.sym(Nat, 1n+dp, Nat.mul(1n+gp, 1n+qdp), ed)
      : {N.Int.mul(N.Int.div_nat(n, 1n+gp), N.Pos{_}) == N.Int.mul(n, N.Pos{1n+qdp}) : N.Int}
    mul_divnat(n, gp, qa, ea, 1n+qdp)))

law red.go:
  for +n: N.Int
  for +dp: Nat
  for +g: Nat
  for +qa: Nat
  for +ea: {N.Int.abs(n) == Nat.mul(g, qa) : Nat}
  for +qd: Nat
  for +ed: {1n+dp == Nat.mul(g, qd) : Nat}
  for great: @k: Nat -> PD.Dv(k, N.Int.abs(n)) -> PD.Dv(k, 1n+dp) -> PD.Dv(k, g)
  L.Canon(N.Rat.reduce.go(n, 1n+dp, g)) & L.Denotes(N.Rat.reduce.go(n, 1n+dp, g), n, N.Pos{1n+dp})

def red.go(n, dp, g, qa, ea, qd, ed, great):
  match g:
    case 0n:
      Empty.absurd(L.Canon(N.Rat.reduce.go(n, 1n+dp, 0n)) & L.Denotes(N.Rat.reduce.go(n, 1n+dp, 0n), n, N.Pos{1n+dp}),
        PD.succ_ne_zero(dp, ed))
    case 1n+gp:
      match qd:
        case 0n:
          Empty.absurd(L.Canon(N.Rat.reduce.go(n, 1n+dp, 1n+gp)) & L.Denotes(N.Rat.reduce.go(n, 1n+dp, 1n+gp), n, N.Pos{1n+dp}),
            PD.succ_ne_zero(dp, (%PN.mul_zero_r(1n+gp) : {1n+dp == _ : Nat}
                                 ed)))
        case 1n+qdp:
          red.go2(n, dp, gp, qa, ea, qdp, ed, great)

law red.split2:
  for +n: N.Int
  for +dp: Nat
  for da: PD.Dv(N.Nat.gcd(N.Int.abs(n), 1n+dp), N.Int.abs(n))
  for dd: PD.Dv(N.Nat.gcd(N.Int.abs(n), 1n+dp), 1n+dp)
  L.Canon(N.Rat.reduce(n, dp)) & L.Denotes(N.Rat.reduce(n, dp), n, N.Pos{1n+dp})

def red.split2(n, dp, da, dd):
  match da:
    case (qa, ea):
      match dd:
        case (qd, ed):
          red.go(n, dp, N.Nat.gcd(N.Int.abs(n), 1n+dp), qa, ea, qd, ed,
            +k => d1 => d2 => PD.gcd_greatest(k, N.Int.abs(n), 1n+dp, d1, d2))

law red.split:
  for +n: N.Int
  for +dp: Nat
  for gd: PD.Dv(N.Nat.gcd(N.Int.abs(n), 1n+dp), N.Int.abs(n)) & PD.Dv(N.Nat.gcd(N.Int.abs(n), 1n+dp), 1n+dp)
  L.Canon(N.Rat.reduce(n, dp)) & L.Denotes(N.Rat.reduce(n, dp), n, N.Pos{1n+dp})

def red.split(n, dp, gd):
  match gd:
    case (da, dd):
      red.split2(n, dp, da, dd)

# reduce(n, dp) is in lowest terms and equals n / (1 + dp).
law reduce_ok:
  for +n: N.Int
  for +dp: Nat
  L.Canon(N.Rat.reduce(n, dp)) & L.Denotes(N.Rat.reduce(n, dp), n, N.Pos{1n+dp})

def reduce_ok(n, dp):
  red.split(n, dp, PD.gcd_dvd(N.Int.abs(n), 1n+dp))

# Uniqueness of lowest terms
# --------------------------

law canon_eq.go:
  for +x: N.Int
  for +p: Nat
  for +y: N.Int
  for +q: Nat
  for ca: @k: Nat -> PD.Dv(k, N.Int.abs(x)) -> PD.Dv(k, 1n+p) -> {k == 1n : Nat}
  for cb: @k: Nat -> PD.Dv(k, N.Int.abs(y)) -> PD.Dv(k, 1n+q) -> {k == 1n : Nat}
  for +h: {N.Int.mul(x, N.Pos{1n+q}) == N.Int.mul(y, N.Pos{1n+p}) : N.Int}
  {N.Rat{x, p} == N.Rat{y, q} : N.Rat}

def canon_eq.go(x, p, y, q, ca, cb, h):
  +ea = Equal.trans(Nat, Nat.mul(N.Int.abs(x), 1n+q), N.Int.abs(N.Int.mul(x, N.Pos{1n+q})), Nat.mul(N.Int.abs(y), 1n+p),
    Equal.sym(Nat, N.Int.abs(N.Int.mul(x, N.Pos{1n+q})), Nat.mul(N.Int.abs(x), 1n+q), abs_mul_pos(x, 1n+q)),
    Equal.trans(Nat, N.Int.abs(N.Int.mul(x, N.Pos{1n+q})), N.Int.abs(N.Int.mul(y, N.Pos{1n+p})), Nat.mul(N.Int.abs(y), 1n+p),
      Equal.cong(N.Int, Nat, z => N.Int.abs(z), N.Int.mul(x, N.Pos{1n+q}), N.Int.mul(y, N.Pos{1n+p}), h),
      abs_mul_pos(y, 1n+p)))
  +epq = PD.dv_antisym(p, q,
    PD.coprime_dvd(N.Int.abs(x), p, q, ca,
      (N.Int.abs(y), Equal.trans(Nat, Nat.mul(N.Int.abs(x), 1n+q), Nat.mul(N.Int.abs(y), 1n+p), Nat.mul(1n+p, N.Int.abs(y)),
        ea, PN.mul_comm(N.Int.abs(y), 1n+p)))),
    PD.coprime_dvd(N.Int.abs(y), q, p, cb,
      (N.Int.abs(x), Equal.trans(Nat, Nat.mul(N.Int.abs(y), 1n+p), Nat.mul(N.Int.abs(x), 1n+q), Nat.mul(1n+q, N.Int.abs(x)),
        Equal.sym(Nat, Nat.mul(N.Int.abs(x), 1n+q), Nat.mul(N.Int.abs(y), 1n+p), ea), PN.mul_comm(N.Int.abs(x), 1n+q)))))
  +ep = PD.succ_inj(p, q, epq)
  %int_cancel(x, y, q,
      (%ep : {N.Int.mul(x, N.Pos{1n+q}) == N.Int.mul(y, N.Pos{1n+_}) : N.Int}
       h))
    : {N.Rat{x, p} == N.Rat{_, q} : N.Rat}
  %ep : {N.Rat{x, p} == N.Rat{x, _} : N.Rat}
  {==}

# Two Rats in lowest terms with the same value are equal.
law canon_eq:
  for a: N.Rat
  for b: N.Rat
  for ca: L.Canon(a)
  for cb: L.Canon(b)
  for h: L.Denotes(a, L.num(b), L.den(b))
  {a == b : N.Rat}

def canon_eq(a, b, ca, cb, h):
  match a b:
    case N.Rat{x, p} N.Rat{y, q}:
      canon_eq.go(x, p, y, q, ca, cb, h)

# Operations
# ----------

law make_ok.z:
  for +n: N.Int
  for e: Empty
  exs r: N.Rat
  {N.Rat.make(n, N.Pos{0n}) == Some{r} : Maybe<N.Rat>} & L.Canon(r) & L.Denotes(r, n, N.Pos{0n})

def make_ok.z(n, e):
  match e:

law mul_negp:
  for +z: N.Int
  for +p: Nat
  {N.Int.mul(z, N.Neg{p}) == N.Int.neg(N.Int.mul(z, N.Pos{1n+p})) : N.Int}

def mul_negp(z, p):
  match z:
    case N.Pos{m}:
      {==}
    case N.Neg{m}:
      {==}

# r == a / (1 + p) with a == -n gives r == n / -(1 + p).
law den_negp:
  for +r: N.Rat
  for +n: N.Int
  for +p: Nat
  for h: L.Denotes(r, N.Int.neg(n), N.Pos{1n+p})
  L.Denotes(r, n, N.Neg{p})

def den_negp(r, n, p, h):
  %Equal.sym(N.Int, N.Int.mul(L.num(r), N.Neg{p}), N.Int.neg(N.Int.mul(L.num(r), N.Pos{1n+p})), mul_negp(L.num(r), p))
    : {_ == N.Int.mul(n, L.den(r)) : N.Int}
  %Equal.sym(N.Int, N.Int.mul(L.num(r), N.Pos{1n+p}), N.Int.mul(N.Int.neg(n), L.den(r)), h)
    : {N.Int.neg(_) == N.Int.mul(n, L.den(r)) : N.Int}
  PI.IRing.eq(PI.INeg{PI.IMul{PI.INeg{PI.IVar{0n}}, PI.IVar{1n}}}, PI.IMul{PI.IVar{0n}, PI.IVar{1n}}, [n, L.den(r)], {==})

law make_ok.neg:
  for +n: N.Int
  for +p: Nat
  for cd: L.Canon(N.Rat.reduce(N.Int.neg(n), p)) & L.Denotes(N.Rat.reduce(N.Int.neg(n), p), N.Int.neg(n), N.Pos{1n+p})
  L.Canon(N.Rat.reduce(N.Int.neg(n), p)) & L.Denotes(N.Rat.reduce(N.Int.neg(n), p), n, N.Neg{p})

def make_ok.neg(n, p, cd):
  match cd:
    case (c, d):
      (c, den_negp(N.Rat.reduce(N.Int.neg(n), p), n, p, d))

law make_ok:
  for +n: N.Int
  for +d: N.Int
  for nz: {d != N.Int.zero() : N.Int}
  exs r: N.Rat
  {N.Rat.make(n, d) == Some{r} : Maybe<N.Rat>} & L.Canon(r) & L.Denotes(r, n, d)

def make_ok(n, d, nz):
  match d:
    case N.Pos{0n}:
      make_ok.z(n, nz({==}))
    case N.Pos{1n+p}:
      (N.Rat.reduce(n, p), ({==}, reduce_ok(n, p)))
    case N.Neg{p}:
      (N.Rat.reduce(N.Int.neg(n), p), ({==}, make_ok.neg(n, p, reduce_ok(N.Int.neg(n), p))))

law of_int.canon:
  for +k: Nat
  for d: PD.Dv(k, 1n)
  {k == 1n : Nat}

def of_int.canon(k, d):
  match d:
    case (t, e):
      PD.mul_eq_one(k, t, Equal.sym(Nat, 1n, Nat.mul(k, t), e))

law of_int_ok:
  for +n: N.Int
  L.Canon(N.Rat.of_int(n)) & L.Denotes(N.Rat.of_int(n), n, N.Int.one())

def of_int_ok(n):
  (+k => d1 => d2 => of_int.canon(k, d2), {==})

law neg_ok:
  for +a: N.Rat
  for ca: L.Canon(a)
  L.Canon(N.Rat.neg(a)) & L.Denotes(N.Rat.neg(a), N.Int.neg(L.num(a)), L.den(a))

def neg_ok(a, ca):
  match a:
    case N.Rat{x, p}:
      (+k => d1 => d2 => ca(k, (%abs_neg(x) : PD.Dv(k, _)
                                d1), d2),
       {==})

law add_ok:
  for +a: N.Rat
  for +b: N.Rat
  L.Canon(N.Rat.add(a, b))
    & L.Denotes(N.Rat.add(a, b), N.Int.add(N.Int.mul(L.num(a), L.den(b)), N.Int.mul(L.num(b), L.den(a))), N.Int.mul(L.den(a), L.den(b)))

def add_ok(a, b):
  match a b:
    case N.Rat{x, p} N.Rat{y, q}:
      reduce_ok(N.Int.add(N.Int.mul(x, N.Pos{1n+q}), N.Int.mul(y, N.Pos{1n+p})), N.Nat.mul_pred(p, q))

law mul_ok:
  for +a: N.Rat
  for +b: N.Rat
  L.Canon(N.Rat.mul(a, b)) & L.Denotes(N.Rat.mul(a, b), N.Int.mul(L.num(a), L.num(b)), N.Int.mul(L.den(a), L.den(b)))

def mul_ok(a, b):
  match a b:
    case N.Rat{x, p} N.Rat{y, q}:
      reduce_ok(N.Int.mul(x, y), N.Nat.mul_pred(p, q))

law sub_ok:
  for +a: N.Rat
  for +b: N.Rat
  L.Canon(N.Rat.sub(a, b))
    & L.Denotes(N.Rat.sub(a, b), N.Int.sub(N.Int.mul(L.num(a), L.den(b)), N.Int.mul(L.num(b), L.den(a))), N.Int.mul(L.den(a), L.den(b)))

def sub_ok(a, b):
  match a b:
    case N.Rat{x, p} N.Rat{y, q}:
      %PI.IRing.eq(
          PI.IAdd{PI.IMul{PI.IVar{0n}, PI.IVar{1n}}, PI.IMul{PI.INeg{PI.IVar{2n}}, PI.IVar{3n}}},
          PI.IAdd{PI.IMul{PI.IVar{0n}, PI.IVar{1n}}, PI.INeg{PI.IMul{PI.IVar{2n}, PI.IVar{3n}}}},
          [x, N.Pos{1n+q}, y, N.Pos{1n+p}], {==})
        : L.Canon(N.Rat.sub(N.Rat{x, p}, N.Rat{y, q}))
            & L.Denotes(N.Rat.sub(N.Rat{x, p}, N.Rat{y, q}), _, N.Int.mul(N.Pos{1n+p}, N.Pos{1n+q}))
      reduce_ok(N.Int.add(N.Int.mul(x, N.Pos{1n+q}), N.Int.mul(N.Int.neg(y), N.Pos{1n+p})), N.Nat.mul_pred(p, q))

law inv_ok.z:
  for +d: Nat
  for e: Empty
  exs r: N.Rat
  {N.Rat.inv(N.Rat{N.Pos{0n}, d}) == Some{r} : Maybe<N.Rat>} & L.Canon(r) & L.Denotes(r, N.Pos{1n+d}, N.Pos{0n})

def inv_ok.z(d, e):
  match e:

law inv_ok:
  for +a: N.Rat
  for ca: L.Canon(a)
  for nz: {L.num(a) != N.Int.zero() : N.Int}
  exs r: N.Rat
  {N.Rat.inv(a) == Some{r} : Maybe<N.Rat>} & L.Canon(r) & L.Denotes(r, L.den(a), L.num(a))

def inv_ok(a, ca, nz):
  match a:
    case N.Rat{N.Pos{0n}, p}:
      inv_ok.z(p, nz({==}))
    case N.Rat{N.Pos{1n+m}, p}:
      (N.Rat{N.Pos{1n+p}, m}, ({==}, (+k => d1 => d2 => ca(k, d2, d1), {==})))
    case N.Rat{N.Neg{m}, p}:
      (N.Rat{N.Neg{p}, m}, ({==}, (+k => d1 => d2 => ca(k, d2, d1), {==})))

law le_def:
  for a: N.Rat
  for b: N.Rat
  {N.Rat.is_le(a, b) == N.Int.is_le(N.Int.mul(L.num(a), L.den(b)), N.Int.mul(L.num(b), L.den(a))) : Bool}

def le_def(a, b):
  match a b:
    case N.Rat{x, p} N.Rat{y, q}:
      {==}

law div_ok.z:
  for +a: N.Rat
  for +q: Nat
  for e: Empty
  exs r: N.Rat
  {N.Rat.div(a, N.Rat{N.Pos{0n}, q}) == Some{r} : Maybe<N.Rat>}
    & L.Canon(r) & L.Denotes(r, N.Int.mul(L.num(a), N.Pos{1n+q}), N.Int.mul(L.den(a), N.Pos{0n}))

def div_ok.z(a, q, e):
  match e:

law den_flip:
  for +r: N.Rat
  for +A: N.Int
  for +B: N.Int
  for +q: Nat
  for +m: Nat
  for h: {N.Int.mul(L.num(r), N.Int.mul(B, N.Pos{1n+m})) == N.Int.mul(N.Int.mul(A, N.Neg{q}), L.den(r)) : N.Int}
  {N.Int.mul(L.num(r), N.Int.mul(B, N.Neg{m})) == N.Int.mul(N.Int.mul(A, N.Pos{1n+q}), L.den(r)) : N.Int}

def den_flip(r, A, B, q, m, h):
  %Equal.sym(N.Int, N.Int.mul(B, N.Neg{m}), N.Int.neg(N.Int.mul(B, N.Pos{1n+m})), mul_negp(B, m))
    : {N.Int.mul(L.num(r), _) == N.Int.mul(N.Int.mul(A, N.Pos{1n+q}), L.den(r)) : N.Int}
  %PI.IRing.eq(
      PI.INeg{PI.IMul{PI.IVar{0n}, PI.IMul{PI.IVar{1n}, PI.IVar{2n}}}},
      PI.IMul{PI.IVar{0n}, PI.INeg{PI.IMul{PI.IVar{1n}, PI.IVar{2n}}}},
      [L.num(r), B, N.Pos{1n+m}], {==})
    : {_ == N.Int.mul(N.Int.mul(A, N.Pos{1n+q}), L.den(r)) : N.Int}
  %Equal.sym(N.Int, N.Int.mul(L.num(r), N.Int.mul(B, N.Pos{1n+m})), N.Int.mul(N.Int.mul(A, N.Neg{q}), L.den(r)), h)
    : {N.Int.neg(_) == N.Int.mul(N.Int.mul(A, N.Pos{1n+q}), L.den(r)) : N.Int}
  %Equal.sym(N.Int, N.Int.mul(A, N.Neg{q}), N.Int.neg(N.Int.mul(A, N.Pos{1n+q})), mul_negp(A, q))
    : {N.Int.neg(N.Int.mul(_, L.den(r))) == N.Int.mul(N.Int.mul(A, N.Pos{1n+q}), L.den(r)) : N.Int}
  PI.IRing.eq(
    PI.INeg{PI.IMul{PI.INeg{PI.IMul{PI.IVar{0n}, PI.IVar{1n}}}, PI.IVar{2n}}},
    PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{1n}}, PI.IVar{2n}},
    [A, N.Pos{1n+q}, L.den(r)], {==})

law div_ok.neg:
  for +a: N.Rat
  for +q: Nat
  for +m: Nat
  for cd: L.Canon(N.Rat.mul(a, N.Rat{N.Neg{q}, m}))
    & L.Denotes(N.Rat.mul(a, N.Rat{N.Neg{q}, m}), N.Int.mul(L.num(a), N.Neg{q}), N.Int.mul(L.den(a), N.Pos{1n+m}))
  L.Canon(N.Rat.mul(a, N.Rat{N.Neg{q}, m}))
    & L.Denotes(N.Rat.mul(a, N.Rat{N.Neg{q}, m}), N.Int.mul(L.num(a), N.Pos{1n+q}), N.Int.mul(L.den(a), N.Neg{m}))

def div_ok.neg(a, q, m, cd):
  match cd:
    case (c, d):
      (c, den_flip(N.Rat.mul(a, N.Rat{N.Neg{q}, m}), L.num(a), L.den(a), q, m, d))

law div_ok:
  for +a: N.Rat
  for +b: N.Rat
  for nz: {L.num(b) != N.Int.zero() : N.Int}
  exs r: N.Rat
  {N.Rat.div(a, b) == Some{r} : Maybe<N.Rat>}
    & L.Canon(r)
    & L.Denotes(r, N.Int.mul(L.num(a), L.den(b)), N.Int.mul(L.den(a), L.num(b)))

def div_ok(a, b, nz):
  match b:
    case N.Rat{N.Pos{0n}, q}:
      div_ok.z(a, q, nz({==}))
    case N.Rat{N.Pos{1n+m}, q}:
      (N.Rat.mul(a, N.Rat{N.Pos{1n+q}, m}), ({==}, mul_ok(a, N.Rat{N.Pos{1n+q}, m})))
    case N.Rat{N.Neg{m}, q}:
      (N.Rat.mul(a, N.Rat{N.Neg{q}, m}), ({==}, div_ok.neg(a, q, m, mul_ok(a, N.Rat{N.Neg{q}, m}))))

# Changing the fraction
# ---------------------

# r == N / (1 + k) and N D2 == N2 (1 + k) give r == N2 / D2.
law den_trans:
  for +r: N.Rat
  for +n: N.Int
  for +k: Nat
  for +n2: N.Int
  for +d2: N.Int
  for h: {N.Int.mul(L.num(r), N.Pos{1n+k}) == N.Int.mul(n, L.den(r)) : N.Int}
  for cross: {N.Int.mul(n, d2) == N.Int.mul(n2, N.Pos{1n+k}) : N.Int}
  L.Denotes(r, n2, d2)

def den_trans(r, n, k, n2, d2, h, cross):
  int_cancel(N.Int.mul(L.num(r), d2), N.Int.mul(n2, L.den(r)), k,
    (%PI.IRing.eq(
         PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{2n}}, PI.IVar{1n}},
         PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{1n}}, PI.IVar{2n}},
         [L.num(r), d2, N.Pos{1n+k}], {==})
       : {_ == N.Int.mul(N.Int.mul(n2, L.den(r)), N.Pos{1n+k}) : N.Int}
     %Equal.sym(N.Int, N.Int.mul(L.num(r), N.Pos{1n+k}), N.Int.mul(n, L.den(r)), h)
       : {N.Int.mul(_, d2) == N.Int.mul(N.Int.mul(n2, L.den(r)), N.Pos{1n+k}) : N.Int}
     %PI.IRing.eq(
         PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{2n}}, PI.IVar{1n}},
         PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{1n}}, PI.IVar{2n}},
         [n, L.den(r), d2], {==})
       : {_ == N.Int.mul(N.Int.mul(n2, L.den(r)), N.Pos{1n+k}) : N.Int}
     %Equal.sym(N.Int, N.Int.mul(n, d2), N.Int.mul(n2, N.Pos{1n+k}), cross)
       : {N.Int.mul(_, L.den(r)) == N.Int.mul(N.Int.mul(n2, L.den(r)), N.Pos{1n+k}) : N.Int}
     PI.IRing.eq(
       PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{1n}}, PI.IVar{2n}},
       PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{2n}}, PI.IVar{1n}},
       [n2, N.Pos{1n+k}, L.den(r)], {==})))

# r1 == N1 / D1, r2 == N2 / D2 and N1 D2 == N2 D1 give r1 == L.num(r2) / L.den(r2).
law den_same:
  for +r1: N.Rat
  for +r2: N.Rat
  for +n1: N.Int
  for +k1: Nat
  for +n2: N.Int
  for +k2: Nat
  for h1: {N.Int.mul(L.num(r1), N.Pos{1n+k1}) == N.Int.mul(n1, L.den(r1)) : N.Int}
  for h2: {N.Int.mul(L.num(r2), N.Pos{1n+k2}) == N.Int.mul(n2, L.den(r2)) : N.Int}
  for cross: {N.Int.mul(n1, N.Pos{1n+k2}) == N.Int.mul(n2, N.Pos{1n+k1}) : N.Int}
  L.Denotes(r1, L.num(r2), L.den(r2))

def den_same(r1, r2, n1, k1, n2, k2, h1, h2, cross):
  int_cancel(N.Int.mul(L.num(r1), L.den(r2)), N.Int.mul(L.num(r2), L.den(r1)), N.Nat.mul_pred(k1, k2),
    (%PI.IRing.eq(
         PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{2n}}, PI.IMul{PI.IVar{1n}, PI.IVar{3n}}},
         PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{1n}}, PI.IMul{PI.IVar{2n}, PI.IVar{3n}}},
         [L.num(r1), L.den(r2), N.Pos{1n+k1}, N.Pos{1n+k2}], {==})
       : {_ == N.Int.mul(N.Int.mul(L.num(r2), L.den(r1)), N.Int.mul(N.Pos{1n+k1}, N.Pos{1n+k2})) : N.Int}
     %PI.IRing.eq(
         PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{3n}}, PI.IMul{PI.IVar{1n}, PI.IVar{2n}}},
         PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{1n}}, PI.IMul{PI.IVar{2n}, PI.IVar{3n}}},
         [L.num(r2), L.den(r1), N.Pos{1n+k1}, N.Pos{1n+k2}], {==})
       : {N.Int.mul(N.Int.mul(L.num(r1), N.Pos{1n+k1}), N.Int.mul(L.den(r2), N.Pos{1n+k2})) == _ : N.Int}
     %Equal.sym(N.Int, N.Int.mul(L.num(r1), N.Pos{1n+k1}), N.Int.mul(n1, L.den(r1)), h1)
       : {N.Int.mul(_, N.Int.mul(L.den(r2), N.Pos{1n+k2}))
           == N.Int.mul(N.Int.mul(L.num(r2), N.Pos{1n+k2}), N.Int.mul(L.den(r1), N.Pos{1n+k1})) : N.Int}
     %Equal.sym(N.Int, N.Int.mul(L.num(r2), N.Pos{1n+k2}), N.Int.mul(n2, L.den(r2)), h2)
       : {N.Int.mul(N.Int.mul(n1, L.den(r1)), N.Int.mul(L.den(r2), N.Pos{1n+k2}))
           == N.Int.mul(_, N.Int.mul(L.den(r1), N.Pos{1n+k1})) : N.Int}
     %PI.IRing.eq(
         PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{3n}}, PI.IMul{PI.IVar{1n}, PI.IVar{2n}}},
         PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{1n}}, PI.IMul{PI.IVar{2n}, PI.IVar{3n}}},
         [n1, L.den(r1), L.den(r2), N.Pos{1n+k2}], {==})
       : {_ == N.Int.mul(N.Int.mul(n2, L.den(r2)), N.Int.mul(L.den(r1), N.Pos{1n+k1})) : N.Int}
     %Equal.sym(N.Int, N.Int.mul(n1, N.Pos{1n+k2}), N.Int.mul(n2, N.Pos{1n+k1}), cross)
       : {N.Int.mul(_, N.Int.mul(L.den(r1), L.den(r2))) == N.Int.mul(N.Int.mul(n2, L.den(r2)), N.Int.mul(L.den(r1), N.Pos{1n+k1})) : N.Int}
     PI.IRing.eq(
       PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{1n}}, PI.IMul{PI.IVar{2n}, PI.IVar{3n}}},
       PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{3n}}, PI.IMul{PI.IVar{2n}, PI.IVar{1n}}},
       [n2, N.Pos{1n+k1}, L.den(r1), L.den(r2)], {==})))

# The value of a sum and of a product
# -----------------------------------

law cd_den:
  for +r: N.Rat
  for +n: N.Int
  for +d: N.Int
  for cd: L.Canon(r) & L.Denotes(r, n, d)
  L.Denotes(r, n, d)

def cd_den(r, n, d, cd):
  match cd:
    case (c, e):
      e

law cd_canon:
  for +r: N.Rat
  for +n: N.Int
  for +d: N.Int
  for cd: L.Canon(r) & L.Denotes(r, n, d)
  L.Canon(r)

def cd_canon(r, n, d, cd):
  match cd:
    case (c, e):
      c

law add_canon:
  for +a: N.Rat
  for +b: N.Rat
  L.Canon(N.Rat.add(a, b))

def add_canon(a, b):
  cd_canon(N.Rat.add(a, b), N.Int.add(N.Int.mul(L.num(a), L.den(b)), N.Int.mul(L.num(b), L.den(a))), N.Int.mul(L.den(a), L.den(b)),
    add_ok(a, b))

law mul_canon:
  for +a: N.Rat
  for +b: N.Rat
  L.Canon(N.Rat.mul(a, b))

def mul_canon(a, b):
  cd_canon(N.Rat.mul(a, b), N.Int.mul(L.num(a), L.num(b)), N.Int.mul(L.den(a), L.den(b)), mul_ok(a, b))

# r1 == n1 / K1 and r2 == n2 / K2 give r1 + r2 == (n1 K2 + n2 K1) / (K1 K2).
law den_add:
  for +r1: N.Rat
  for +r2: N.Rat
  for +n1: N.Int
  for +k1: Nat
  for +n2: N.Int
  for +k2: Nat
  for h1: {N.Int.mul(L.num(r1), N.Pos{1n+k1}) == N.Int.mul(n1, L.den(r1)) : N.Int}
  for h2: {N.Int.mul(L.num(r2), N.Pos{1n+k2}) == N.Int.mul(n2, L.den(r2)) : N.Int}
  {N.Int.mul(L.num(N.Rat.add(r1, r2)), N.Pos{1n+N.Nat.mul_pred(k1, k2)})
    == N.Int.mul(N.Int.add(N.Int.mul(n1, N.Pos{1n+k2}), N.Int.mul(n2, N.Pos{1n+k1})), L.den(N.Rat.add(r1, r2))) : N.Int}

def den_add(r1, r2, n1, k1, n2, k2, h1, h2):
  match r1 r2:
    case N.Rat{x, p} N.Rat{y, q}:
      den_trans(N.Rat.add(N.Rat{x, p}, N.Rat{y, q}),
        N.Int.add(N.Int.mul(x, N.Pos{1n+q}), N.Int.mul(y, N.Pos{1n+p})), N.Nat.mul_pred(p, q),
        N.Int.add(N.Int.mul(n1, N.Pos{1n+k2}), N.Int.mul(n2, N.Pos{1n+k1})), N.Pos{1n+N.Nat.mul_pred(k1, k2)},
        cd_den(N.Rat.add(N.Rat{x, p}, N.Rat{y, q}),
          N.Int.add(N.Int.mul(x, N.Pos{1n+q}), N.Int.mul(y, N.Pos{1n+p})), N.Int.mul(N.Pos{1n+p}, N.Pos{1n+q}),
          add_ok(N.Rat{x, p}, N.Rat{y, q})),
        (%PI.IRing.eq(
             PI.IAdd{PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{6n}}, PI.IMul{PI.IVar{5n}, PI.IVar{7n}}},
                     PI.IMul{PI.IMul{PI.IVar{1n}, PI.IVar{7n}}, PI.IMul{PI.IVar{4n}, PI.IVar{6n}}}},
             PI.IMul{PI.IAdd{PI.IMul{PI.IVar{0n}, PI.IVar{5n}}, PI.IMul{PI.IVar{1n}, PI.IVar{4n}}}, PI.IMul{PI.IVar{6n}, PI.IVar{7n}}},
             [x, y, n1, n2, N.Pos{1n+p}, N.Pos{1n+q}, N.Pos{1n+k1}, N.Pos{1n+k2}], {==})
           : {_ == N.Int.mul(N.Int.add(N.Int.mul(n1, N.Pos{1n+k2}), N.Int.mul(n2, N.Pos{1n+k1})),
                             N.Int.mul(N.Pos{1n+p}, N.Pos{1n+q})) : N.Int}
         %Equal.sym(N.Int, N.Int.mul(x, N.Pos{1n+k1}), N.Int.mul(n1, N.Pos{1n+p}), h1)
           : {N.Int.add(N.Int.mul(_, N.Int.mul(N.Pos{1n+q}, N.Pos{1n+k2})),
                        N.Int.mul(N.Int.mul(y, N.Pos{1n+k2}), N.Int.mul(N.Pos{1n+p}, N.Pos{1n+k1})))
               == N.Int.mul(N.Int.add(N.Int.mul(n1, N.Pos{1n+k2}), N.Int.mul(n2, N.Pos{1n+k1})),
                            N.Int.mul(N.Pos{1n+p}, N.Pos{1n+q})) : N.Int}
         %Equal.sym(N.Int, N.Int.mul(y, N.Pos{1n+k2}), N.Int.mul(n2, N.Pos{1n+q}), h2)
           : {N.Int.add(N.Int.mul(N.Int.mul(n1, N.Pos{1n+p}), N.Int.mul(N.Pos{1n+q}, N.Pos{1n+k2})),
                        N.Int.mul(_, N.Int.mul(N.Pos{1n+p}, N.Pos{1n+k1})))
               == N.Int.mul(N.Int.add(N.Int.mul(n1, N.Pos{1n+k2}), N.Int.mul(n2, N.Pos{1n+k1})),
                            N.Int.mul(N.Pos{1n+p}, N.Pos{1n+q})) : N.Int}
         PI.IRing.eq(
           PI.IAdd{PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{2n}}, PI.IMul{PI.IVar{3n}, PI.IVar{5n}}},
                   PI.IMul{PI.IMul{PI.IVar{1n}, PI.IVar{3n}}, PI.IMul{PI.IVar{2n}, PI.IVar{4n}}}},
           PI.IMul{PI.IAdd{PI.IMul{PI.IVar{0n}, PI.IVar{5n}}, PI.IMul{PI.IVar{1n}, PI.IVar{4n}}}, PI.IMul{PI.IVar{2n}, PI.IVar{3n}}},
           [n1, n2, N.Pos{1n+p}, N.Pos{1n+q}, N.Pos{1n+k1}, N.Pos{1n+k2}], {==})))

# r1 == n1 / K1 and r2 == n2 / K2 give r1 r2 == (n1 n2) / (K1 K2).
law den_mul:
  for +r1: N.Rat
  for +r2: N.Rat
  for +n1: N.Int
  for +k1: Nat
  for +n2: N.Int
  for +k2: Nat
  for h1: {N.Int.mul(L.num(r1), N.Pos{1n+k1}) == N.Int.mul(n1, L.den(r1)) : N.Int}
  for h2: {N.Int.mul(L.num(r2), N.Pos{1n+k2}) == N.Int.mul(n2, L.den(r2)) : N.Int}
  {N.Int.mul(L.num(N.Rat.mul(r1, r2)), N.Pos{1n+N.Nat.mul_pred(k1, k2)})
    == N.Int.mul(N.Int.mul(n1, n2), L.den(N.Rat.mul(r1, r2))) : N.Int}

def den_mul(r1, r2, n1, k1, n2, k2, h1, h2):
  match r1 r2:
    case N.Rat{x, p} N.Rat{y, q}:
      den_trans(N.Rat.mul(N.Rat{x, p}, N.Rat{y, q}), N.Int.mul(x, y), N.Nat.mul_pred(p, q),
        N.Int.mul(n1, n2), N.Pos{1n+N.Nat.mul_pred(k1, k2)},
        cd_den(N.Rat.mul(N.Rat{x, p}, N.Rat{y, q}), N.Int.mul(x, y), N.Int.mul(N.Pos{1n+p}, N.Pos{1n+q}),
          mul_ok(N.Rat{x, p}, N.Rat{y, q})),
        (%PI.IRing.eq(
             PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{2n}}, PI.IMul{PI.IVar{1n}, PI.IVar{3n}}},
             PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{1n}}, PI.IMul{PI.IVar{2n}, PI.IVar{3n}}},
             [x, y, N.Pos{1n+k1}, N.Pos{1n+k2}], {==})
           : {_ == N.Int.mul(N.Int.mul(n1, n2), N.Int.mul(N.Pos{1n+p}, N.Pos{1n+q})) : N.Int}
         %Equal.sym(N.Int, N.Int.mul(x, N.Pos{1n+k1}), N.Int.mul(n1, N.Pos{1n+p}), h1)
           : {N.Int.mul(_, N.Int.mul(y, N.Pos{1n+k2})) == N.Int.mul(N.Int.mul(n1, n2), N.Int.mul(N.Pos{1n+p}, N.Pos{1n+q})) : N.Int}
         %Equal.sym(N.Int, N.Int.mul(y, N.Pos{1n+k2}), N.Int.mul(n2, N.Pos{1n+q}), h2)
           : {N.Int.mul(N.Int.mul(n1, N.Pos{1n+p}), _) == N.Int.mul(N.Int.mul(n1, n2), N.Int.mul(N.Pos{1n+p}, N.Pos{1n+q})) : N.Int}
         PI.IRing.eq(
           PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{2n}}, PI.IMul{PI.IVar{1n}, PI.IVar{3n}}},
           PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{1n}}, PI.IMul{PI.IVar{2n}, PI.IVar{3n}}},
           [n1, n2, N.Pos{1n+p}, N.Pos{1n+q}], {==})))

# Field laws
# ----------

law mp_comm:
  for +p: Nat
  for +q: Nat
  {N.Nat.mul_pred(p, q) == N.Nat.mul_pred(q, p) : Nat}

def mp_comm(p, q):
  R.Ring.eq(
    R.EAdd{R.EVar{1n}, R.EMul{R.EVar{0n}, R.EAdd{R.ENum{1n}, R.EVar{1n}}}},
    R.EAdd{R.EVar{0n}, R.EMul{R.EVar{1n}, R.EAdd{R.ENum{1n}, R.EVar{0n}}}},
    [p, q], {==})

law add_comm:
  for +a: N.Rat
  for +b: N.Rat
  {N.Rat.add(a, b) == N.Rat.add(b, a) : N.Rat}

def add_comm(a, b):
  match a b:
    case N.Rat{x, p} N.Rat{y, q}:
      %PI.Int.add_comm(N.Int.mul(x, N.Pos{1n+q}), N.Int.mul(y, N.Pos{1n+p}))
        : {N.Rat.reduce(N.Int.add(N.Int.mul(x, N.Pos{1n+q}), N.Int.mul(y, N.Pos{1n+p})), N.Nat.mul_pred(p, q))
            == N.Rat.reduce(_, N.Nat.mul_pred(q, p)) : N.Rat}
      %mp_comm(p, q)
        : {N.Rat.reduce(N.Int.add(N.Int.mul(x, N.Pos{1n+q}), N.Int.mul(y, N.Pos{1n+p})), N.Nat.mul_pred(p, q))
            == N.Rat.reduce(N.Int.add(N.Int.mul(x, N.Pos{1n+q}), N.Int.mul(y, N.Pos{1n+p})), _) : N.Rat}
      {==}

law mul_comm:
  for +a: N.Rat
  for +b: N.Rat
  {N.Rat.mul(a, b) == N.Rat.mul(b, a) : N.Rat}

def mul_comm(a, b):
  match a b:
    case N.Rat{x, p} N.Rat{y, q}:
      %PI.Int.mul_comm(x, y)
        : {N.Rat.reduce(N.Int.mul(x, y), N.Nat.mul_pred(p, q)) == N.Rat.reduce(_, N.Nat.mul_pred(q, p)) : N.Rat}
      %mp_comm(p, q)
        : {N.Rat.reduce(N.Int.mul(x, y), N.Nat.mul_pred(p, q)) == N.Rat.reduce(N.Int.mul(x, y), _) : N.Rat}
      {==}

law add_zero:
  for +a: N.Rat
  for ca: L.Canon(a)
  {N.Rat.add(a, N.Rat.zero()) == a : N.Rat}

def add_zero(a, ca):
  match a:
    case N.Rat{x, p}:
      canon_eq(N.Rat.add(N.Rat{x, p}, N.Rat.zero()), N.Rat{x, p}, add_canon(N.Rat{x, p}, N.Rat.zero()), ca,
        den_trans(N.Rat.add(N.Rat{x, p}, N.Rat.zero()),
          N.Int.add(N.Int.mul(x, N.Pos{1n}), N.Int.mul(N.Pos{0n}, N.Pos{1n+p})), N.Nat.mul_pred(p, 0n),
          x, N.Pos{1n+p},
          cd_den(N.Rat.add(N.Rat{x, p}, N.Rat.zero()),
            N.Int.add(N.Int.mul(x, N.Pos{1n}), N.Int.mul(N.Pos{0n}, N.Pos{1n+p})), N.Int.mul(N.Pos{1n+p}, N.Pos{1n}),
            add_ok(N.Rat{x, p}, N.Rat.zero())),
          PI.IRing.eq(
            PI.IMul{PI.IAdd{PI.IMul{PI.IVar{0n}, PI.IConst{N.Pos{1n}}}, PI.IMul{PI.IConst{N.Pos{0n}}, PI.IVar{1n}}}, PI.IVar{1n}},
            PI.IMul{PI.IVar{0n}, PI.IMul{PI.IVar{1n}, PI.IConst{N.Pos{1n}}}},
            [x, N.Pos{1n+p}], {==})))

law mul_one:
  for +a: N.Rat
  for ca: L.Canon(a)
  {N.Rat.mul(a, N.Rat.one()) == a : N.Rat}

def mul_one(a, ca):
  match a:
    case N.Rat{x, p}:
      canon_eq(N.Rat.mul(N.Rat{x, p}, N.Rat.one()), N.Rat{x, p}, mul_canon(N.Rat{x, p}, N.Rat.one()), ca,
        den_trans(N.Rat.mul(N.Rat{x, p}, N.Rat.one()), N.Int.mul(x, N.Pos{1n}), N.Nat.mul_pred(p, 0n),
          x, N.Pos{1n+p},
          cd_den(N.Rat.mul(N.Rat{x, p}, N.Rat.one()), N.Int.mul(x, N.Pos{1n}), N.Int.mul(N.Pos{1n+p}, N.Pos{1n}),
            mul_ok(N.Rat{x, p}, N.Rat.one())),
          PI.IRing.eq(
            PI.IMul{PI.IMul{PI.IVar{0n}, PI.IConst{N.Pos{1n}}}, PI.IVar{1n}},
            PI.IMul{PI.IVar{0n}, PI.IMul{PI.IVar{1n}, PI.IConst{N.Pos{1n}}}},
            [x, N.Pos{1n+p}], {==})))

law add_neg:
  for +a: N.Rat
  {N.Rat.add(a, N.Rat.neg(a)) == N.Rat.zero() : N.Rat}

def add_neg(a):
  match a:
    case N.Rat{x, p}:
      canon_eq(N.Rat.add(N.Rat{x, p}, N.Rat{N.Int.neg(x), p}), N.Rat.zero(),
        add_canon(N.Rat{x, p}, N.Rat{N.Int.neg(x), p}),
        cd_canon(N.Rat.zero(), N.Pos{0n}, N.Int.one(), of_int_ok(N.Pos{0n})),
        den_trans(N.Rat.add(N.Rat{x, p}, N.Rat{N.Int.neg(x), p}),
          N.Int.add(N.Int.mul(x, N.Pos{1n+p}), N.Int.mul(N.Int.neg(x), N.Pos{1n+p})), N.Nat.mul_pred(p, p),
          N.Pos{0n}, N.Pos{1n},
          cd_den(N.Rat.add(N.Rat{x, p}, N.Rat{N.Int.neg(x), p}),
            N.Int.add(N.Int.mul(x, N.Pos{1n+p}), N.Int.mul(N.Int.neg(x), N.Pos{1n+p})), N.Int.mul(N.Pos{1n+p}, N.Pos{1n+p}),
            add_ok(N.Rat{x, p}, N.Rat{N.Int.neg(x), p})),
          PI.IRing.eq(
            PI.IMul{PI.IAdd{PI.IMul{PI.IVar{0n}, PI.IVar{1n}}, PI.IMul{PI.INeg{PI.IVar{0n}}, PI.IVar{1n}}}, PI.IConst{N.Pos{1n}}},
            PI.IMul{PI.IConst{N.Pos{0n}}, PI.IMul{PI.IVar{1n}, PI.IVar{1n}}},
            [x, N.Pos{1n+p}], {==})))

law add_assoc:
  for +a: N.Rat
  for +b: N.Rat
  for +c: N.Rat
  {N.Rat.add(N.Rat.add(a, b), c) == N.Rat.add(a, N.Rat.add(b, c)) : N.Rat}

def add_assoc(a, b, c):
  match a b c:
    case N.Rat{x, p} N.Rat{y, q} N.Rat{z, s}:
      canon_eq(
        N.Rat.add(N.Rat.add(N.Rat{x, p}, N.Rat{y, q}), N.Rat{z, s}),
        N.Rat.add(N.Rat{x, p}, N.Rat.add(N.Rat{y, q}, N.Rat{z, s})),
        add_canon(N.Rat.add(N.Rat{x, p}, N.Rat{y, q}), N.Rat{z, s}),
        add_canon(N.Rat{x, p}, N.Rat.add(N.Rat{y, q}, N.Rat{z, s})),
        den_same(
          N.Rat.add(N.Rat.add(N.Rat{x, p}, N.Rat{y, q}), N.Rat{z, s}),
          N.Rat.add(N.Rat{x, p}, N.Rat.add(N.Rat{y, q}, N.Rat{z, s})),
          N.Int.add(N.Int.mul(N.Int.add(N.Int.mul(x, N.Pos{1n+q}), N.Int.mul(y, N.Pos{1n+p})), N.Pos{1n+s}),
                    N.Int.mul(z, N.Pos{1n+N.Nat.mul_pred(p, q)})),
          N.Nat.mul_pred(N.Nat.mul_pred(p, q), s),
          N.Int.add(N.Int.mul(x, N.Pos{1n+N.Nat.mul_pred(q, s)}),
                    N.Int.mul(N.Int.add(N.Int.mul(y, N.Pos{1n+s}), N.Int.mul(z, N.Pos{1n+q})), N.Pos{1n+p})),
          N.Nat.mul_pred(p, N.Nat.mul_pred(q, s)),
          den_add(N.Rat.add(N.Rat{x, p}, N.Rat{y, q}), N.Rat{z, s},
            N.Int.add(N.Int.mul(x, N.Pos{1n+q}), N.Int.mul(y, N.Pos{1n+p})), N.Nat.mul_pred(p, q), z, s,
            den_add(N.Rat{x, p}, N.Rat{y, q}, x, p, y, q, {==}, {==}), {==}),
          den_add(N.Rat{x, p}, N.Rat.add(N.Rat{y, q}, N.Rat{z, s}),
            x, p, N.Int.add(N.Int.mul(y, N.Pos{1n+s}), N.Int.mul(z, N.Pos{1n+q})), N.Nat.mul_pred(q, s),
            {==}, den_add(N.Rat{y, q}, N.Rat{z, s}, y, q, z, s, {==}, {==})),
          PI.IRing.eq(
            PI.IMul{PI.IAdd{PI.IMul{PI.IAdd{PI.IMul{PI.IVar{0n}, PI.IVar{4n}}, PI.IMul{PI.IVar{1n}, PI.IVar{3n}}}, PI.IVar{5n}},
                            PI.IMul{PI.IVar{2n}, PI.IMul{PI.IVar{3n}, PI.IVar{4n}}}},
                    PI.IMul{PI.IVar{3n}, PI.IMul{PI.IVar{4n}, PI.IVar{5n}}}},
            PI.IMul{PI.IAdd{PI.IMul{PI.IVar{0n}, PI.IMul{PI.IVar{4n}, PI.IVar{5n}}},
                            PI.IMul{PI.IAdd{PI.IMul{PI.IVar{1n}, PI.IVar{5n}}, PI.IMul{PI.IVar{2n}, PI.IVar{4n}}}, PI.IVar{3n}}},
                    PI.IMul{PI.IMul{PI.IVar{3n}, PI.IVar{4n}}, PI.IVar{5n}}},
            [x, y, z, N.Pos{1n+p}, N.Pos{1n+q}, N.Pos{1n+s}], {==})))

law mul_assoc:
  for +a: N.Rat
  for +b: N.Rat
  for +c: N.Rat
  {N.Rat.mul(N.Rat.mul(a, b), c) == N.Rat.mul(a, N.Rat.mul(b, c)) : N.Rat}

def mul_assoc(a, b, c):
  match a b c:
    case N.Rat{x, p} N.Rat{y, q} N.Rat{z, s}:
      canon_eq(
        N.Rat.mul(N.Rat.mul(N.Rat{x, p}, N.Rat{y, q}), N.Rat{z, s}),
        N.Rat.mul(N.Rat{x, p}, N.Rat.mul(N.Rat{y, q}, N.Rat{z, s})),
        mul_canon(N.Rat.mul(N.Rat{x, p}, N.Rat{y, q}), N.Rat{z, s}),
        mul_canon(N.Rat{x, p}, N.Rat.mul(N.Rat{y, q}, N.Rat{z, s})),
        den_same(
          N.Rat.mul(N.Rat.mul(N.Rat{x, p}, N.Rat{y, q}), N.Rat{z, s}),
          N.Rat.mul(N.Rat{x, p}, N.Rat.mul(N.Rat{y, q}, N.Rat{z, s})),
          N.Int.mul(N.Int.mul(x, y), z), N.Nat.mul_pred(N.Nat.mul_pred(p, q), s),
          N.Int.mul(x, N.Int.mul(y, z)), N.Nat.mul_pred(p, N.Nat.mul_pred(q, s)),
          den_mul(N.Rat.mul(N.Rat{x, p}, N.Rat{y, q}), N.Rat{z, s}, N.Int.mul(x, y), N.Nat.mul_pred(p, q), z, s,
            den_mul(N.Rat{x, p}, N.Rat{y, q}, x, p, y, q, {==}, {==}), {==}),
          den_mul(N.Rat{x, p}, N.Rat.mul(N.Rat{y, q}, N.Rat{z, s}), x, p, N.Int.mul(y, z), N.Nat.mul_pred(q, s),
            {==}, den_mul(N.Rat{y, q}, N.Rat{z, s}, y, q, z, s, {==}, {==})),
          PI.IRing.eq(
            PI.IMul{PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{1n}}, PI.IVar{2n}}, PI.IMul{PI.IVar{3n}, PI.IMul{PI.IVar{4n}, PI.IVar{5n}}}},
            PI.IMul{PI.IMul{PI.IVar{0n}, PI.IMul{PI.IVar{1n}, PI.IVar{2n}}}, PI.IMul{PI.IMul{PI.IVar{3n}, PI.IVar{4n}}, PI.IVar{5n}}},
            [x, y, z, N.Pos{1n+p}, N.Pos{1n+q}, N.Pos{1n+s}], {==})))

law mul_add:
  for +a: N.Rat
  for +b: N.Rat
  for +c: N.Rat
  {N.Rat.mul(a, N.Rat.add(b, c)) == N.Rat.add(N.Rat.mul(a, b), N.Rat.mul(a, c)) : N.Rat}

def mul_add(a, b, c):
  match a b c:
    case N.Rat{x, p} N.Rat{y, q} N.Rat{z, s}:
      canon_eq(
        N.Rat.mul(N.Rat{x, p}, N.Rat.add(N.Rat{y, q}, N.Rat{z, s})),
        N.Rat.add(N.Rat.mul(N.Rat{x, p}, N.Rat{y, q}), N.Rat.mul(N.Rat{x, p}, N.Rat{z, s})),
        mul_canon(N.Rat{x, p}, N.Rat.add(N.Rat{y, q}, N.Rat{z, s})),
        add_canon(N.Rat.mul(N.Rat{x, p}, N.Rat{y, q}), N.Rat.mul(N.Rat{x, p}, N.Rat{z, s})),
        den_same(
          N.Rat.mul(N.Rat{x, p}, N.Rat.add(N.Rat{y, q}, N.Rat{z, s})),
          N.Rat.add(N.Rat.mul(N.Rat{x, p}, N.Rat{y, q}), N.Rat.mul(N.Rat{x, p}, N.Rat{z, s})),
          N.Int.mul(x, N.Int.add(N.Int.mul(y, N.Pos{1n+s}), N.Int.mul(z, N.Pos{1n+q}))),
          N.Nat.mul_pred(p, N.Nat.mul_pred(q, s)),
          N.Int.add(N.Int.mul(N.Int.mul(x, y), N.Pos{1n+N.Nat.mul_pred(p, s)}),
                    N.Int.mul(N.Int.mul(x, z), N.Pos{1n+N.Nat.mul_pred(p, q)})),
          N.Nat.mul_pred(N.Nat.mul_pred(p, q), N.Nat.mul_pred(p, s)),
          den_mul(N.Rat{x, p}, N.Rat.add(N.Rat{y, q}, N.Rat{z, s}),
            x, p, N.Int.add(N.Int.mul(y, N.Pos{1n+s}), N.Int.mul(z, N.Pos{1n+q})), N.Nat.mul_pred(q, s),
            {==}, den_add(N.Rat{y, q}, N.Rat{z, s}, y, q, z, s, {==}, {==})),
          den_add(N.Rat.mul(N.Rat{x, p}, N.Rat{y, q}), N.Rat.mul(N.Rat{x, p}, N.Rat{z, s}),
            N.Int.mul(x, y), N.Nat.mul_pred(p, q), N.Int.mul(x, z), N.Nat.mul_pred(p, s),
            den_mul(N.Rat{x, p}, N.Rat{y, q}, x, p, y, q, {==}, {==}),
            den_mul(N.Rat{x, p}, N.Rat{z, s}, x, p, z, s, {==}, {==})),
          PI.IRing.eq(
            PI.IMul{PI.IMul{PI.IVar{0n}, PI.IAdd{PI.IMul{PI.IVar{1n}, PI.IVar{5n}}, PI.IMul{PI.IVar{2n}, PI.IVar{4n}}}},
                    PI.IMul{PI.IMul{PI.IVar{3n}, PI.IVar{4n}}, PI.IMul{PI.IVar{3n}, PI.IVar{5n}}}},
            PI.IMul{PI.IAdd{PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{1n}}, PI.IMul{PI.IVar{3n}, PI.IVar{5n}}},
                            PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{2n}}, PI.IMul{PI.IVar{3n}, PI.IVar{4n}}}},
                    PI.IMul{PI.IVar{3n}, PI.IMul{PI.IVar{4n}, PI.IVar{5n}}}},
            [x, y, z, N.Pos{1n+p}, N.Pos{1n+q}, N.Pos{1n+s}], {==})))
