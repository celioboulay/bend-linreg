import Base
import ./num.bend as N
import ./p_nat.bend as PN
import ./p_int.bend as PI
import ./p_ring.bend as R

# Order, subtraction, division and gcd on Nat.

def Bool.td(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

law Bool.ft:
  for e: {False{} == True{} : Bool}
  Empty

def Bool.ft(e):
  %Equal.sym(Bool, False{}, True{}, e) : Bool.td(_)
  Unit{}

# Order
# -----

law lt_zero:
  for +x: Nat
  for h: {Nat.is_lt(x, 0n) == True{} : Bool}
  Empty

def lt_zero(x, h):
  match x:
    case 0n:
      Bool.ft(h)
    case 1n+p:
      Bool.ft(h)

law le_lt_trans:
  for +x: Nat
  for +y: Nat
  for +z: Nat
  for h1: {Nat.is_le(x, y) == True{} : Bool}
  for h2: {Nat.is_lt(y, z) == True{} : Bool}
  {Nat.is_lt(x, z) == True{} : Bool}

def le_lt_trans(x, y, z, h1, h2):
  match x y z:
    case 0n _ 0n:
      Empty.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, lt_zero(y, h2))
    case 0n _ 1n+s:
      {==}
    case 1n+p 0n _:
      Empty.absurd({Nat.is_lt(1n+p, z) == True{} : Bool}, Bool.ft(h1))
    case 1n+p 1n+q 0n:
      Empty.absurd({Nat.is_lt(1n+p, 0n) == True{} : Bool}, lt_zero(1n+q, h2))
    case 1n+p 1n+q 1n+s:
      le_lt_trans(p, q, s, h1, h2)

# x < 1 + x + k
law lt_plus:
  for +x: Nat
  for +k: Nat
  {Nat.is_lt(x, 1n+Nat.add(x, k)) == True{} : Bool}

def lt_plus(x, k):
  match x:
    case 0n:
      {==}
    case 1n+p:
      lt_plus(p, k)

# x <= x + k
law le_plus:
  for +x: Nat
  for +k: Nat
  {Nat.is_le(x, Nat.add(x, k)) == True{} : Bool}

def le_plus(x, k):
  match x:
    case 0n:
      match k:
        case 0n:
          {==}
        case 1n+j:
          {==}
    case 1n+p:
      le_plus(p, k)

# Subtraction
# -----------

law sub_add_l:
  for +k: Nat
  for +x: Nat
  for +y: Nat
  {Nat.sub(Nat.add(k, x), Nat.add(k, y)) == Nat.sub(x, y) : Nat}

def sub_add_l(k, x, y):
  match k:
    case 0n:
      {==}
    case 1n+j:
      sub_add_l(j, x, y)

# (x + y) - x == y
law sub_add_self:
  for +x: Nat
  for +y: Nat
  {Nat.sub(Nat.add(x, y), x) == y : Nat}

def sub_add_self(x, y):
  match x:
    case 0n:
      PI.Nat.sub_zero_r(y)
    case 1n+p:
      sub_add_self(p, y)

law mul_sub:
  for +k: Nat
  for +m: Nat
  for +n: Nat
  {Nat.mul(k, Nat.sub(m, n)) == Nat.sub(Nat.mul(k, m), Nat.mul(k, n)) : Nat}

def mul_sub(k, m, n):
  match m n:
    case 0n _:
      %Equal.sym(Nat, Nat.mul(k, 0n), 0n, PN.mul_zero_r(k)) : {_ == Nat.sub(_, Nat.mul(k, n)) : Nat}
      {==}
    case 1n+p 0n:
      %Equal.sym(Nat, Nat.mul(k, 0n), 0n, PN.mul_zero_r(k))
        : {Nat.mul(k, 1n+p) == Nat.sub(Nat.mul(k, 1n+p), _) : Nat}
      Equal.sym(Nat, Nat.sub(Nat.mul(k, 1n+p), 0n), Nat.mul(k, 1n+p), PI.Nat.sub_zero_r(Nat.mul(k, 1n+p)))
    case 1n+p 1n+q:
      %Equal.sym(Nat, Nat.mul(k, 1n+p), Nat.add(k, Nat.mul(k, p)), PN.mul_succ_r(k, p))
        : {Nat.mul(k, Nat.sub(p, q)) == Nat.sub(_, Nat.mul(k, 1n+q)) : Nat}
      %Equal.sym(Nat, Nat.mul(k, 1n+q), Nat.add(k, Nat.mul(k, q)), PN.mul_succ_r(k, q))
        : {Nat.mul(k, Nat.sub(p, q)) == Nat.sub(Nat.add(k, Nat.mul(k, p)), _) : Nat}
      %Equal.sym(Nat, Nat.sub(Nat.add(k, Nat.mul(k, p)), Nat.add(k, Nat.mul(k, q))), Nat.sub(Nat.mul(k, p), Nat.mul(k, q)),
          sub_add_l(k, Nat.mul(k, p), Nat.mul(k, q)))
        : {Nat.mul(k, Nat.sub(p, q)) == _ : Nat}
      mul_sub(k, p, q)

# Division
# --------
# Base's divmod.go counts n down; m + r == bp is its loop invariant, with
# divisor 1 + bp.

law dm_sum:
  for +n: Nat
  for +m: Nat
  for +d: Nat
  for +r: Nat
  for +bp: Nat
  for +inv: {Nat.add(m, r) == bp : Nat}
  {Nat.add(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(n, m, d, r)), 1n+bp), Pair.snd(Nat, Nat, Nat.divmod.go(n, m, d, r)))
    == Nat.add(Nat.add(Nat.mul(d, 1n+bp), r), n) : Nat}

def dm_sum(n, m, d, r, bp, inv):
  match n:
    case 0n:
      Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(d, 1n+bp), r), 0n), Nat.add(Nat.mul(d, 1n+bp), r),
        PN.add_zero_r(Nat.add(Nat.mul(d, 1n+bp), r)))
    case 1n+np:
      match m:
        case 0n:
          %Equal.sym(Nat,
              Nat.add(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(np, r, 1n+d, 0n)), 1n+bp), Pair.snd(Nat, Nat, Nat.divmod.go(np, r, 1n+d, 0n))),
              Nat.add(Nat.add(Nat.mul(1n+d, 1n+bp), 0n), np),
              dm_sum(np, r, 1n+d, 0n, bp, Equal.trans(Nat, Nat.add(r, 0n), r, bp, PN.add_zero_r(r), inv)))
            : {_ == Nat.add(Nat.add(Nat.mul(d, 1n+bp), r), 1n+np) : Nat}
          %Equal.sym(Nat, r, bp, inv)
            : {Nat.add(Nat.add(Nat.mul(1n+d, 1n+bp), 0n), np) == Nat.add(Nat.add(Nat.mul(d, 1n+bp), _), 1n+np) : Nat}
          R.Ring.eq(
            R.EAdd{R.EAdd{R.EMul{R.EAdd{R.ENum{1n}, R.EVar{0n}}, R.EAdd{R.ENum{1n}, R.EVar{1n}}}, R.ENum{0n}}, R.EVar{2n}},
            R.EAdd{R.EAdd{R.EMul{R.EVar{0n}, R.EAdd{R.ENum{1n}, R.EVar{1n}}}, R.EVar{1n}}, R.EAdd{R.ENum{1n}, R.EVar{2n}}},
            [d, bp, np], {==})
        case 1n+mp:
          %Equal.sym(Nat,
              Nat.add(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(np, mp, d, 1n+r)), 1n+bp), Pair.snd(Nat, Nat, Nat.divmod.go(np, mp, d, 1n+r))),
              Nat.add(Nat.add(Nat.mul(d, 1n+bp), 1n+r), np),
              dm_sum(np, mp, d, 1n+r, bp, Equal.trans(Nat, Nat.add(mp, 1n+r), 1n+Nat.add(mp, r), bp, PN.add_succ_r(mp, r), inv)))
            : {_ == Nat.add(Nat.add(Nat.mul(d, 1n+bp), r), 1n+np) : Nat}
          R.Ring.eq(
            R.EAdd{R.EAdd{R.EMul{R.EVar{0n}, R.EAdd{R.ENum{1n}, R.EVar{1n}}}, R.EAdd{R.ENum{1n}, R.EVar{2n}}}, R.EVar{3n}},
            R.EAdd{R.EAdd{R.EMul{R.EVar{0n}, R.EAdd{R.ENum{1n}, R.EVar{1n}}}, R.EVar{2n}}, R.EAdd{R.ENum{1n}, R.EVar{3n}}},
            [d, bp, r, np], {==})

law dm_le:
  for +n: Nat
  for +m: Nat
  for +d: Nat
  for +r: Nat
  for +bp: Nat
  for inv: {Nat.add(m, r) == bp : Nat}
  {Nat.is_le(Pair.snd(Nat, Nat, Nat.divmod.go(n, m, d, r)), bp) == True{} : Bool}

def dm_le(n, m, d, r, bp, inv):
  match n:
    case 0n:
      %Equal.trans(Nat, Nat.add(r, m), Nat.add(m, r), bp, PN.add_comm(r, m), inv) : {Nat.is_le(r, _) == True{} : Bool}
      le_plus(r, m)
    case 1n+np:
      match m:
        case 0n:
          dm_le(np, r, 1n+d, 0n, bp, Equal.trans(Nat, Nat.add(r, 0n), r, bp, PN.add_zero_r(r), inv))
        case 1n+mp:
          dm_le(np, mp, d, 1n+r, bp, Equal.trans(Nat, Nat.add(mp, 1n+r), 1n+Nat.add(mp, r), bp, PN.add_succ_r(mp, r), inv))

# a == (a / b) b + a % b, for b = 1 + bp
law div_mod:
  for +a: Nat
  for +bp: Nat
  {Nat.add(Nat.mul(Nat.div(a, 1n+bp), 1n+bp), Nat.mod(a, 1n+bp)) == a : Nat}

def div_mod(a, bp):
  dm_sum(a, bp, 0n, 0n, bp, PN.add_zero_r(bp))

# a % b <= b - 1
law mod_le:
  for +a: Nat
  for +bp: Nat
  {Nat.is_le(Nat.mod(a, 1n+bp), bp) == True{} : Bool}

def mod_le(a, bp):
  dm_le(a, bp, 0n, 0n, bp, PN.add_zero_r(bp))

# gcd
# ---

def Dv(k: Nat, n: Nat) -> Type:
  &q: Nat -> {n == Nat.mul(k, q) : Nat}

law dv_refl:
  for +a: Nat
  Dv(a, a)

def dv_refl(a):
  (1n, Equal.sym(Nat, Nat.mul(a, 1n), a, PN.mul_one_r(a)))

law dv_zero:
  for +a: Nat
  Dv(a, 0n)

def dv_zero(a):
  (0n, Equal.sym(Nat, Nat.mul(a, 0n), 0n, PN.mul_zero_r(a)))

law lt_succ:
  for +b: Nat
  {Nat.is_lt(b, 1n+b) == True{} : Bool}

def lt_succ(b):
  match b:
    case 0n:
      {==}
    case 1n+p:
      lt_succ(p)

# g | b and g | a % b give g | a.
law dv_euclid:
  for +a: Nat
  for +bp: Nat
  for +g: Nat
  for db: Dv(g, 1n+bp)
  for dm: Dv(g, Nat.mod(a, 1n+bp))
  Dv(g, a)

def dv_euclid(a, bp, g, db, dm):
  match db:
    case (+qb, eb):
      match dm:
        case (+qm, em):
          (Nat.add(Nat.mul(Nat.div(a, 1n+bp), qb), qm),
            (%div_mod(a, bp) : {_ == Nat.mul(g, Nat.add(Nat.mul(Nat.div(a, 1n+bp), qb), qm)) : Nat}
             %Equal.sym(Nat, 1n+bp, Nat.mul(g, qb), eb)
               : {Nat.add(Nat.mul(Nat.div(a, 1n+bp), _), Nat.mod(a, 1n+bp))
                   == Nat.mul(g, Nat.add(Nat.mul(Nat.div(a, 1n+bp), qb), qm)) : Nat}
             %Equal.sym(Nat, Nat.mod(a, 1n+bp), Nat.mul(g, qm), em)
               : {Nat.add(Nat.mul(Nat.div(a, 1n+bp), Nat.mul(g, qb)), _)
                   == Nat.mul(g, Nat.add(Nat.mul(Nat.div(a, 1n+bp), qb), qm)) : Nat}
             R.Ring.eq(
               R.EAdd{R.EMul{R.EVar{0n}, R.EMul{R.EVar{1n}, R.EVar{2n}}}, R.EMul{R.EVar{1n}, R.EVar{3n}}},
               R.EMul{R.EVar{1n}, R.EAdd{R.EMul{R.EVar{0n}, R.EVar{2n}}, R.EVar{3n}}},
               [Nat.div(a, 1n+bp), g, qb, qm], {==})))

# k | a and k | b give k | a % b, on the parts of the two witnesses.
law dv_mod.eq:
  for +a: Nat
  for +bp: Nat
  for +k: Nat
  for +qa: Nat
  for ea: {a == Nat.mul(k, qa) : Nat}
  for +qb: Nat
  for eb: {1n+bp == Nat.mul(k, qb) : Nat}
  {Nat.mod(a, 1n+bp) == Nat.mul(k, Nat.sub(qa, Nat.mul(Nat.div(a, 1n+bp), qb))) : Nat}

def dv_mod.eq(a, bp, k, qa, ea, qb, eb):
  %Equal.sym(Nat, Nat.mul(k, Nat.sub(qa, Nat.mul(Nat.div(a, 1n+bp), qb))),
      Nat.sub(Nat.mul(k, qa), Nat.mul(k, Nat.mul(Nat.div(a, 1n+bp), qb))),
      mul_sub(k, qa, Nat.mul(Nat.div(a, 1n+bp), qb)))
    : {Nat.mod(a, 1n+bp) == _ : Nat}
  %Equal.sym(Nat, Nat.mul(k, Nat.mul(Nat.div(a, 1n+bp), qb)), Nat.mul(Nat.div(a, 1n+bp), Nat.mul(k, qb)),
      PN.mul_left_comm(k, Nat.div(a, 1n+bp), qb))
    : {Nat.mod(a, 1n+bp) == Nat.sub(Nat.mul(k, qa), _) : Nat}
  %ea : {Nat.mod(a, 1n+bp) == Nat.sub(_, Nat.mul(Nat.div(a, 1n+bp), Nat.mul(k, qb))) : Nat}
  %eb : {Nat.mod(a, 1n+bp) == Nat.sub(a, Nat.mul(Nat.div(a, 1n+bp), _)) : Nat}
  %div_mod(a, bp) : {Nat.mod(a, 1n+bp) == Nat.sub(_, Nat.mul(Nat.div(a, 1n+bp), 1n+bp)) : Nat}
  Equal.sym(Nat,
    Nat.sub(Nat.add(Nat.mul(Nat.div(a, 1n+bp), 1n+bp), Nat.mod(a, 1n+bp)), Nat.mul(Nat.div(a, 1n+bp), 1n+bp)),
    Nat.mod(a, 1n+bp),
    sub_add_self(Nat.mul(Nat.div(a, 1n+bp), 1n+bp), Nat.mod(a, 1n+bp)))

law dv_dup.go:
  for +k: Nat
  for +n: Nat
  for +q: Nat
  for +e: {n == Nat.mul(k, q) : Nat}
  Dv(k, n) & Dv(k, n)

def dv_dup.go(k, n, q, e):
  ((q, e), (q, e))

# Two copies of a divisibility witness (a witness is a pair, so it is
# used once; its parts can be reused).
law dv_dup:
  for +k: Nat
  for +n: Nat
  for d: Dv(k, n)
  Dv(k, n) & Dv(k, n)

def dv_dup(k, n, d):
  match d:
    case (+q, e):
      dv_dup.go(k, n, q, e)

law gcd_dvd.both:
  for +a: Nat
  for +bp: Nat
  for +g: Nat
  for dd: Dv(g, 1n+bp) & Dv(g, 1n+bp)
  for dm: Dv(g, Nat.mod(a, 1n+bp))
  Dv(g, a) & Dv(g, 1n+bp)

def gcd_dvd.both(a, bp, g, dd, dm):
  match dd:
    case (d1, d2):
      (dv_euclid(a, bp, g, d1, dm), d2)

law gcd_dvd.step:
  for +a: Nat
  for +bp: Nat
  for +g: Nat
  for ih: Dv(g, 1n+bp) & Dv(g, Nat.mod(a, 1n+bp))
  Dv(g, a) & Dv(g, 1n+bp)

def gcd_dvd.step(a, bp, g, ih):
  match ih:
    case (db, dm):
      gcd_dvd.both(a, bp, g, dv_dup(g, 1n+bp, db), dm)

law gcd_dvd.go:
  for +f: Nat
  for +a: Nat
  for +b: Nat
  for h: {Nat.is_lt(b, f) == True{} : Bool}
  Dv(N.Nat.gcd.go(f, a, b), a) & Dv(N.Nat.gcd.go(f, a, b), b)

def gcd_dvd.go(f, a, b, h):
  match f:
    case 0n:
      Empty.absurd(Dv(a, a) & Dv(a, b), lt_zero(b, h))
    case 1n+g:
      match b:
        case 0n:
          (dv_refl(a), dv_zero(a))
        case 1n+bp:
          gcd_dvd.step(a, bp, N.Nat.gcd.go(g, 1n+bp, Nat.mod(a, 1n+bp)),
            gcd_dvd.go(g, 1n+bp, Nat.mod(a, 1n+bp), le_lt_trans(Nat.mod(a, 1n+bp), bp, g, mod_le(a, bp), h)))

law gcd_greatest.go:
  for +f: Nat
  for +k: Nat
  for +a: Nat
  for +b: Nat
  for h: {Nat.is_lt(b, f) == True{} : Bool}
  for +qa: Nat
  for +ea: {a == Nat.mul(k, qa) : Nat}
  for +qb: Nat
  for +eb: {b == Nat.mul(k, qb) : Nat}
  Dv(k, N.Nat.gcd.go(f, a, b))

def gcd_greatest.go(f, k, a, b, h, qa, ea, qb, eb):
  match f:
    case 0n:
      Empty.absurd(Dv(k, a), lt_zero(b, h))
    case 1n+g:
      match b:
        case 0n:
          (qa, ea)
        case 1n+bp:
          gcd_greatest.go(g, k, 1n+bp, Nat.mod(a, 1n+bp),
            le_lt_trans(Nat.mod(a, 1n+bp), bp, g, mod_le(a, bp), h),
            qb, eb, Nat.sub(qa, Nat.mul(Nat.div(a, 1n+bp), qb)), dv_mod.eq(a, bp, k, qa, ea, qb, eb))

law gcd_fuel.go:
  for +f1: Nat
  for +f2: Nat
  for +a: Nat
  for +b: Nat
  for h1: {Nat.is_lt(b, f1) == True{} : Bool}
  for h2: {Nat.is_lt(b, f2) == True{} : Bool}
  {N.Nat.gcd.go(f1, a, b) == N.Nat.gcd.go(f2, a, b) : Nat}

def gcd_fuel.go(f1, f2, a, b, h1, h2):
  match f1 f2:
    case 0n _:
      Empty.absurd({a == N.Nat.gcd.go(f2, a, b) : Nat}, lt_zero(b, h1))
    case 1n+g1 0n:
      Empty.absurd({N.Nat.gcd.go(1n+g1, a, b) == a : Nat}, lt_zero(b, h2))
    case 1n+g1 1n+g2:
      match b:
        case 0n:
          {==}
        case 1n+bp:
          gcd_fuel.go(g1, g2, 1n+bp, Nat.mod(a, 1n+bp),
            le_lt_trans(Nat.mod(a, 1n+bp), bp, g1, mod_le(a, bp), h1),
            le_lt_trans(Nat.mod(a, 1n+bp), bp, g2, mod_le(a, bp), h2))

law gcd_dvd:
  for +a: Nat
  for +b: Nat
  Dv(N.Nat.gcd(a, b), a) & Dv(N.Nat.gcd(a, b), b)

def gcd_dvd(a, b):
  gcd_dvd.go(1n+b, a, b, lt_succ(b))

law gcd_greatest:
  for +k: Nat
  for +a: Nat
  for +b: Nat
  for ka: Dv(k, a)
  for kb: Dv(k, b)
  Dv(k, N.Nat.gcd(a, b))

def gcd_greatest(k, a, b, ka, kb):
  match ka:
    case (qa, ea):
      match kb:
        case (qb, eb):
          gcd_greatest.go(1n+b, k, a, b, lt_succ(b), qa, ea, qb, eb)

law gcd_fuel:
  for +k: Nat
  for +a: Nat
  for +b: Nat
  {N.Nat.gcd.go(Nat.add(k, 1n+b), a, b) == N.Nat.gcd(a, b) : Nat}

def gcd_fuel(k, a, b):
  gcd_fuel.go(Nat.add(k, 1n+b), 1n+b, a, b,
    (%Equal.sym(Nat, Nat.add(k, 1n+b), 1n+Nat.add(k, b), PN.add_succ_r(k, b)) : {Nat.is_lt(b, _) == True{} : Bool}
     %Equal.sym(Nat, Nat.add(k, b), Nat.add(b, k), PN.add_comm(k, b)) : {Nat.is_lt(b, 1n+_) == True{} : Bool}
     lt_plus(b, k)),
    lt_succ(b))

# Cancellation and uniqueness
# ---------------------------

def Nat.isz(n: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+p:
      Empty

law zero_ne_succ:
  for +n: Nat
  for e: {0n == 1n+n : Nat}
  Empty

def zero_ne_succ(n, e):
  %e : Nat.isz(_)
  Unit{}

def Nat.pr(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

law succ_inj:
  for +a: Nat
  for +b: Nat
  for e: {1n+a == 1n+b : Nat}
  {a == b : Nat}

def succ_inj(a, b, e):
  Equal.cong(Nat, Nat, n => Nat.pr(n), 1n+a, 1n+b, e)

law add_left_cancel:
  for +k: Nat
  for +x: Nat
  for +y: Nat
  for e: {Nat.add(k, x) == Nat.add(k, y) : Nat}
  {x == y : Nat}

def add_left_cancel(k, x, y, e):
  match k:
    case 0n:
      e
    case 1n+j:
      add_left_cancel(j, x, y, succ_inj(Nat.add(j, x), Nat.add(j, y), e))

law mul_cancel_r:
  for +g: Nat
  for +x: Nat
  for +y: Nat
  for e: {Nat.mul(x, 1n+g) == Nat.mul(y, 1n+g) : Nat}
  {x == y : Nat}

def mul_cancel_r(g, x, y, e):
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, zero_ne_succ(Nat.add(g, Nat.mul(q, 1n+g)), e))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat},
        zero_ne_succ(Nat.add(g, Nat.mul(p, 1n+g)),
          Equal.sym(Nat, 1n+Nat.add(g, Nat.mul(p, 1n+g)), 0n, e)))
    case 1n+p 1n+q:
      %mul_cancel_r(g, p, q, add_left_cancel(1n+g, Nat.mul(p, 1n+g), Nat.mul(q, 1n+g), e)) : {1n+p == 1n+_ : Nat}
      {==}

law succ_ne_zero:
  for +n: Nat
  for e: {1n+n == 0n : Nat}
  Empty

def succ_ne_zero(n, e):
  zero_ne_succ(n, Equal.sym(Nat, 1n+n, 0n, e))

law mul_eq_one.go:
  for +j: Nat
  for +s: Nat
  for e: {Nat.add(s, Nat.mul(j, 1n+s)) == 0n : Nat}
  {1n+j == 1n : Nat}

def mul_eq_one.go(j, s, e):
  match j:
    case 0n:
      {==}
    case 1n+i:
      Empty.absurd({2n+i == 1n : Nat},
        succ_ne_zero(Nat.add(s, Nat.add(s, Nat.mul(i, 1n+s))),
          Equal.trans(Nat, 1n+Nat.add(s, Nat.add(s, Nat.mul(i, 1n+s))), Nat.add(s, 1n+Nat.add(s, Nat.mul(i, 1n+s))), 0n,
            Equal.sym(Nat, Nat.add(s, 1n+Nat.add(s, Nat.mul(i, 1n+s))), 1n+Nat.add(s, Nat.add(s, Nat.mul(i, 1n+s))),
              PN.add_succ_r(s, Nat.add(s, Nat.mul(i, 1n+s)))),
            e)))

law mul_eq_one:
  for +k: Nat
  for +t: Nat
  for e: {Nat.mul(k, t) == 1n : Nat}
  {k == 1n : Nat}

def mul_eq_one(k, t, e):
  match k t:
    case 0n _:
      Empty.absurd({0n == 1n : Nat}, zero_ne_succ(0n, e))
    case 1n+j 0n:
      Empty.absurd({1n+j == 1n : Nat},
        zero_ne_succ(0n, Equal.trans(Nat, 0n, Nat.mul(j, 0n), 1n,
          Equal.sym(Nat, Nat.mul(j, 0n), 0n, PN.mul_zero_r(j)), e)))
    case 1n+j 1n+s:
      mul_eq_one.go(j, s, succ_inj(Nat.add(s, Nat.mul(j, 1n+s)), 0n, e))

# x <= y as an explicit gap: y == x + k
def LeW(x: Nat, y: Nat) -> Type:
  &k: Nat -> {y == Nat.add(x, k) : Nat}

law le_witness.succ:
  for +x: Nat
  for +y: Nat
  for w: LeW(x, y)
  LeW(1n+x, 1n+y)

def le_witness.succ(x, y, w):
  match w:
    case (+k, e):
      (k, (%e : {1n+y == 1n+_ : Nat}
           {==}))

law le_witness:
  for +x: Nat
  for +y: Nat
  for h: {Nat.is_le(x, y) == True{} : Bool}
  LeW(x, y)

def le_witness(x, y, h):
  match x y:
    case 0n _:
      (y, {==})
    case 1n+p 0n:
      Empty.absurd(LeW(1n+p, 0n), Bool.ft(h))
    case 1n+p 1n+q:
      le_witness.succ(p, q, le_witness(p, q, h))

law le_zero_l:
  for +b: Nat
  {Nat.is_le(0n, b) == True{} : Bool}

def le_zero_l(b):
  match b:
    case 0n:
      {==}
    case 1n+p:
      {==}

law big_absurd:
  for +bp: Nat
  for +w: Nat
  for h: {Nat.is_le(1n+Nat.add(bp, w), bp) == True{} : Bool}
  Empty

def big_absurd(bp, w, h):
  match bp:
    case 0n:
      Bool.ft(h)
    case 1n+b:
      big_absurd(b, w, h)

# q b + r == d b + m with r, m < b gives q == d.
law uniq_q:
  for +q: Nat
  for +r: Nat
  for +d: Nat
  for +m: Nat
  for +bp: Nat
  for e: {Nat.add(Nat.mul(q, 1n+bp), r) == Nat.add(Nat.mul(d, 1n+bp), m) : Nat}
  for hr: {Nat.is_le(r, bp) == True{} : Bool}
  for hm: {Nat.is_le(m, bp) == True{} : Bool}
  {q == d : Nat}

def uniq_q(q, r, d, m, bp, e, hr, hm):
  match q d:
    case 0n 0n:
      {==}
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat},
        big_absurd(bp, Nat.add(Nat.mul(p, 1n+bp), r),
          (%PN.add_assoc(bp, Nat.mul(p, 1n+bp), r) : {Nat.is_le(1n+_, bp) == True{} : Bool}
           %Equal.sym(Nat, 1n+Nat.add(Nat.add(bp, Nat.mul(p, 1n+bp)), r), m, e) : {Nat.is_le(_, bp) == True{} : Bool}
           hm)))
    case 0n 1n+s:
      Empty.absurd({0n == 1n+s : Nat},
        big_absurd(bp, Nat.add(Nat.mul(s, 1n+bp), m),
          (%PN.add_assoc(bp, Nat.mul(s, 1n+bp), m) : {Nat.is_le(1n+_, bp) == True{} : Bool}
           %e : {Nat.is_le(_, bp) == True{} : Bool}
           hr)))
    case 1n+p 1n+s:
      %uniq_q(p, r, s, m, bp,
          add_left_cancel(bp, Nat.add(Nat.mul(p, 1n+bp), r), Nat.add(Nat.mul(s, 1n+bp), m),
            Equal.trans(Nat, Nat.add(bp, Nat.add(Nat.mul(p, 1n+bp), r)), Nat.add(Nat.add(bp, Nat.mul(p, 1n+bp)), r),
              Nat.add(bp, Nat.add(Nat.mul(s, 1n+bp), m)),
              Equal.sym(Nat, Nat.add(Nat.add(bp, Nat.mul(p, 1n+bp)), r), Nat.add(bp, Nat.add(Nat.mul(p, 1n+bp), r)),
                PN.add_assoc(bp, Nat.mul(p, 1n+bp), r)),
              Equal.trans(Nat, Nat.add(Nat.add(bp, Nat.mul(p, 1n+bp)), r), Nat.add(Nat.add(bp, Nat.mul(s, 1n+bp)), m),
                Nat.add(bp, Nat.add(Nat.mul(s, 1n+bp), m)),
                succ_inj(Nat.add(Nat.add(bp, Nat.mul(p, 1n+bp)), r), Nat.add(Nat.add(bp, Nat.mul(s, 1n+bp)), m), e),
                PN.add_assoc(bp, Nat.mul(s, 1n+bp), m)))),
          hr, hm)
        : {1n+p == 1n+_ : Nat}
      {==}

law div_exact:
  for +q: Nat
  for +bp: Nat
  {Nat.div(Nat.mul(q, 1n+bp), 1n+bp) == q : Nat}

def div_exact(q, bp):
  Equal.sym(Nat, q, Nat.div(Nat.mul(q, 1n+bp), 1n+bp),
    uniq_q(q, 0n, Nat.div(Nat.mul(q, 1n+bp), 1n+bp), Nat.mod(Nat.mul(q, 1n+bp), 1n+bp), bp,
      Equal.trans(Nat, Nat.add(Nat.mul(q, 1n+bp), 0n), Nat.mul(q, 1n+bp),
        Nat.add(Nat.mul(Nat.div(Nat.mul(q, 1n+bp), 1n+bp), 1n+bp), Nat.mod(Nat.mul(q, 1n+bp), 1n+bp)),
        PN.add_zero_r(Nat.mul(q, 1n+bp)),
        Equal.sym(Nat, Nat.add(Nat.mul(Nat.div(Nat.mul(q, 1n+bp), 1n+bp), 1n+bp), Nat.mod(Nat.mul(q, 1n+bp), 1n+bp)),
          Nat.mul(q, 1n+bp), div_mod(Nat.mul(q, 1n+bp), bp))),
      le_zero_l(bp), mod_le(Nat.mul(q, 1n+bp), bp)))

# d b + s == x with s < b gives x % b == s.
law mod_unique:
  for +d: Nat
  for +s: Nat
  for +bp: Nat
  for +x: Nat
  for +e: {Nat.add(Nat.mul(d, 1n+bp), s) == x : Nat}
  for hs: {Nat.is_le(s, bp) == True{} : Bool}
  {Nat.mod(x, 1n+bp) == s : Nat}

def mod_unique(d, s, bp, x, e, hs):
  Equal.sym(Nat, s, Nat.mod(x, 1n+bp),
    add_left_cancel(Nat.mul(Nat.div(x, 1n+bp), 1n+bp), s, Nat.mod(x, 1n+bp),
      (%uniq_q(d, s, Nat.div(x, 1n+bp), Nat.mod(x, 1n+bp), bp,
           Equal.trans(Nat, Nat.add(Nat.mul(d, 1n+bp), s), x,
             Nat.add(Nat.mul(Nat.div(x, 1n+bp), 1n+bp), Nat.mod(x, 1n+bp)),
             e, Equal.sym(Nat, Nat.add(Nat.mul(Nat.div(x, 1n+bp), 1n+bp), Nat.mod(x, 1n+bp)), x, div_mod(x, bp))),
           hs, mod_le(x, bp))
         : {Nat.add(Nat.mul(_, 1n+bp), s) == Nat.add(Nat.mul(Nat.div(x, 1n+bp), 1n+bp), Nat.mod(x, 1n+bp)) : Nat}
       Equal.trans(Nat, Nat.add(Nat.mul(d, 1n+bp), s), x,
         Nat.add(Nat.mul(Nat.div(x, 1n+bp), 1n+bp), Nat.mod(x, 1n+bp)),
         e, Equal.sym(Nat, Nat.add(Nat.mul(Nat.div(x, 1n+bp), 1n+bp), Nat.mod(x, 1n+bp)), x, div_mod(x, bp))))))

# Scaling
# -------

law lt_le:
  for +r: Nat
  for +g: Nat
  for h: {Nat.is_lt(r, g) == True{} : Bool}
  {Nat.is_le(1n+r, g) == True{} : Bool}

def lt_le(r, g, h):
  match r g:
    case _ 0n:
      Empty.absurd({Nat.is_le(1n+r, 0n) == True{} : Bool}, lt_zero(r, h))
    case 0n 1n+t:
      le_zero_l(t)
    case 1n+p 1n+t:
      lt_le(p, t, h)

law lt_le_trans:
  for +x: Nat
  for +y: Nat
  for +z: Nat
  for h1: {Nat.is_lt(x, y) == True{} : Bool}
  for h2: {Nat.is_le(y, z) == True{} : Bool}
  {Nat.is_lt(x, z) == True{} : Bool}

def lt_le_trans(x, y, z, h1, h2):
  match x y z:
    case _ 0n _:
      Empty.absurd({Nat.is_lt(x, z) == True{} : Bool}, lt_zero(x, h1))
    case _ 1n+q 0n:
      Empty.absurd({Nat.is_lt(x, 0n) == True{} : Bool}, Bool.ft(h2))
    case 0n 1n+q 1n+s:
      {==}
    case 1n+p 1n+q 1n+s:
      lt_le_trans(p, q, s, h1, h2)

law lt_mul.go:
  for +qq: Nat
  for +r: Nat
  for +g: Nat
  for w: LeW(1n+r, g)
  {Nat.is_lt(Nat.mul(1n+qq, r), Nat.mul(1n+qq, g)) == True{} : Bool}

def lt_mul.go(qq, r, g, w):
  match w:
    case (+k, ek):
      %Equal.sym(Nat, g, Nat.add(1n+r, k), ek)
        : {Nat.is_lt(Nat.mul(1n+qq, r), Nat.mul(1n+qq, _)) == True{} : Bool}
      %Equal.sym(Nat, Nat.mul(1n+qq, Nat.add(1n+r, k)),
          1n+Nat.add(Nat.mul(1n+qq, r), Nat.add(qq, Nat.mul(1n+qq, k))),
          R.Ring.eq(
            R.EMul{R.EAdd{R.ENum{1n}, R.EVar{0n}}, R.EAdd{R.EAdd{R.ENum{1n}, R.EVar{1n}}, R.EVar{2n}}},
            R.EAdd{R.ENum{1n}, R.EAdd{R.EMul{R.EAdd{R.ENum{1n}, R.EVar{0n}}, R.EVar{1n}},
                                     R.EAdd{R.EVar{0n}, R.EMul{R.EAdd{R.ENum{1n}, R.EVar{0n}}, R.EVar{2n}}}}},
            [qq, r, k], {==}))
        : {Nat.is_lt(Nat.mul(1n+qq, r), _) == True{} : Bool}
      lt_plus(Nat.mul(1n+qq, r), Nat.add(qq, Nat.mul(1n+qq, k)))

# r < g gives Q r < Q g for Q = 1 + qq.
law lt_mul:
  for +qq: Nat
  for +r: Nat
  for +g: Nat
  for h: {Nat.is_lt(r, g) == True{} : Bool}
  {Nat.is_lt(Nat.mul(1n+qq, r), Nat.mul(1n+qq, g)) == True{} : Bool}

def lt_mul(qq, r, g, h):
  lt_mul.go(qq, r, g, le_witness(1n+r, g, lt_le(r, g, h)))

law mod_scale.le:
  for +qq: Nat
  for +pp: Nat
  for +r: Nat
  for w: LeW(r, pp)
  {Nat.is_le(Nat.mul(1n+qq, r), Nat.add(pp, Nat.mul(qq, 1n+pp))) == True{} : Bool}

def mod_scale.le(qq, pp, r, w):
  match w:
    case (+k, ek):
      %Equal.sym(Nat, pp, Nat.add(r, k), ek)
        : {Nat.is_le(Nat.mul(1n+qq, r), Nat.add(_, Nat.mul(qq, 1n+_))) == True{} : Bool}
      %Equal.sym(Nat, Nat.add(Nat.add(r, k), Nat.mul(qq, 1n+Nat.add(r, k))),
          Nat.add(Nat.mul(1n+qq, r), Nat.add(k, Nat.mul(qq, 1n+k))),
          R.Ring.eq(
            R.EAdd{R.EAdd{R.EVar{1n}, R.EVar{2n}}, R.EMul{R.EVar{0n}, R.EAdd{R.ENum{1n}, R.EAdd{R.EVar{1n}, R.EVar{2n}}}}},
            R.EAdd{R.EMul{R.EAdd{R.ENum{1n}, R.EVar{0n}}, R.EVar{1n}}, R.EAdd{R.EVar{2n}, R.EMul{R.EVar{0n}, R.EAdd{R.ENum{1n}, R.EVar{2n}}}}},
            [qq, r, k], {==}))
        : {Nat.is_le(Nat.mul(1n+qq, r), _) == True{} : Bool}
      le_plus(Nat.mul(1n+qq, r), Nat.add(k, Nat.mul(qq, 1n+k)))

# (Q x) % (Q P) == Q (x % P), for Q = 1 + qq and P = 1 + pp.
law mod_scale:
  for +qq: Nat
  for +x: Nat
  for +pp: Nat
  {Nat.mod(Nat.mul(1n+qq, x), Nat.mul(1n+qq, 1n+pp)) == Nat.mul(1n+qq, Nat.mod(x, 1n+pp)) : Nat}

def mod_scale(qq, x, pp):
  mod_unique(Nat.div(x, 1n+pp), Nat.mul(1n+qq, Nat.mod(x, 1n+pp)), Nat.add(pp, Nat.mul(qq, 1n+pp)), Nat.mul(1n+qq, x),
    (%div_mod(x, pp)
        : {Nat.add(Nat.mul(Nat.div(x, 1n+pp), Nat.mul(1n+qq, 1n+pp)), Nat.mul(1n+qq, Nat.mod(x, 1n+pp)))
            == Nat.mul(1n+qq, _) : Nat}
     R.Ring.eq(
       R.EAdd{R.EMul{R.EVar{2n}, R.EMul{R.EAdd{R.ENum{1n}, R.EVar{0n}}, R.EAdd{R.ENum{1n}, R.EVar{1n}}}},
              R.EMul{R.EAdd{R.ENum{1n}, R.EVar{0n}}, R.EVar{3n}}},
       R.EMul{R.EAdd{R.ENum{1n}, R.EVar{0n}}, R.EAdd{R.EMul{R.EVar{2n}, R.EAdd{R.ENum{1n}, R.EVar{1n}}}, R.EVar{3n}}},
       [qq, pp, Nat.div(x, 1n+pp), Nat.mod(x, 1n+pp)], {==})),
    mod_scale.le(qq, pp, Nat.mod(x, 1n+pp), le_witness(Nat.mod(x, 1n+pp), pp, mod_le(x, pp))))

# Q g <= g + qq (1 + g)
law fuel_le:
  for +qq: Nat
  for +g: Nat
  {Nat.is_le(Nat.mul(1n+qq, g), Nat.add(g, Nat.mul(qq, 1n+g))) == True{} : Bool}

def fuel_le(qq, g):
  %Equal.sym(Nat, Nat.add(g, Nat.mul(qq, 1n+g)), Nat.add(Nat.mul(1n+qq, g), qq),
      R.Ring.eq(
        R.EAdd{R.EVar{1n}, R.EMul{R.EVar{0n}, R.EAdd{R.ENum{1n}, R.EVar{1n}}}},
        R.EAdd{R.EMul{R.EAdd{R.ENum{1n}, R.EVar{0n}}, R.EVar{1n}}, R.EVar{0n}},
        [qq, g], {==}))
    : {Nat.is_le(Nat.mul(1n+qq, g), _) == True{} : Bool}
  le_plus(Nat.mul(1n+qq, g), qq)

law gcd_mul.go:
  for +f: Nat
  for +qq: Nat
  for +x: Nat
  for +p: Nat
  for +h: {Nat.is_lt(p, f) == True{} : Bool}
  {N.Nat.gcd.go(Nat.mul(1n+qq, f), Nat.mul(1n+qq, x), Nat.mul(1n+qq, p))
    == Nat.mul(1n+qq, N.Nat.gcd.go(f, x, p)) : Nat}

def gcd_mul.go(f, qq, x, p, h):
  match f:
    case 0n:
      Empty.absurd({N.Nat.gcd.go(Nat.mul(1n+qq, 0n), Nat.mul(1n+qq, x), Nat.mul(1n+qq, p)) == Nat.mul(1n+qq, x) : Nat},
        lt_zero(p, h))
    case 1n+g:
      match p:
        case 0n:
          %Equal.sym(Nat, Nat.mul(qq, 0n), 0n, PN.mul_zero_r(qq))
            : {N.Nat.gcd.go(Nat.mul(1n+qq, 1n+g), Nat.mul(1n+qq, x), _) == Nat.mul(1n+qq, x) : Nat}
          {==}
        case 1n+pp:
          %Equal.sym(Nat, Nat.mod(Nat.mul(1n+qq, x), Nat.mul(1n+qq, 1n+pp)), Nat.mul(1n+qq, Nat.mod(x, 1n+pp)),
              mod_scale(qq, x, pp))
            : {N.Nat.gcd.go(Nat.add(g, Nat.mul(qq, 1n+g)), Nat.mul(1n+qq, 1n+pp), _)
                == Nat.mul(1n+qq, N.Nat.gcd.go(g, 1n+pp, Nat.mod(x, 1n+pp))) : Nat}
          %Equal.sym(Nat,
              N.Nat.gcd.go(Nat.add(g, Nat.mul(qq, 1n+g)), Nat.mul(1n+qq, 1n+pp), Nat.mul(1n+qq, Nat.mod(x, 1n+pp))),
              N.Nat.gcd.go(Nat.mul(1n+qq, g), Nat.mul(1n+qq, 1n+pp), Nat.mul(1n+qq, Nat.mod(x, 1n+pp))),
              gcd_fuel.go(Nat.add(g, Nat.mul(qq, 1n+g)), Nat.mul(1n+qq, g), Nat.mul(1n+qq, 1n+pp), Nat.mul(1n+qq, Nat.mod(x, 1n+pp)),
                lt_le_trans(Nat.mul(1n+qq, Nat.mod(x, 1n+pp)), Nat.mul(1n+qq, g), Nat.add(g, Nat.mul(qq, 1n+g)),
                  lt_mul(qq, Nat.mod(x, 1n+pp), g, le_lt_trans(Nat.mod(x, 1n+pp), pp, g, mod_le(x, pp), h)),
                  fuel_le(qq, g)),
                lt_mul(qq, Nat.mod(x, 1n+pp), g, le_lt_trans(Nat.mod(x, 1n+pp), pp, g, mod_le(x, pp), h))))
            : {_ == Nat.mul(1n+qq, N.Nat.gcd.go(g, 1n+pp, Nat.mod(x, 1n+pp))) : Nat}
          gcd_mul.go(g, qq, 1n+pp, Nat.mod(x, 1n+pp), le_lt_trans(Nat.mod(x, 1n+pp), pp, g, mod_le(x, pp), h))

# gcd(Q x, Q p) == Q gcd(x, p), for Q = 1 + qq
law gcd_mul:
  for +qq: Nat
  for +x: Nat
  for +p: Nat
  {N.Nat.gcd(Nat.mul(1n+qq, x), Nat.mul(1n+qq, p)) == Nat.mul(1n+qq, N.Nat.gcd(x, p)) : Nat}

def gcd_mul(qq, x, p):
  Equal.trans(Nat,
    N.Nat.gcd.go(1n+Nat.mul(1n+qq, p), Nat.mul(1n+qq, x), Nat.mul(1n+qq, p)),
    N.Nat.gcd.go(Nat.mul(1n+qq, 1n+p), Nat.mul(1n+qq, x), Nat.mul(1n+qq, p)),
    Nat.mul(1n+qq, N.Nat.gcd.go(1n+p, x, p)),
    gcd_fuel.go(1n+Nat.mul(1n+qq, p), Nat.mul(1n+qq, 1n+p), Nat.mul(1n+qq, x), Nat.mul(1n+qq, p),
      lt_succ(Nat.mul(1n+qq, p)), lt_mul(qq, p, 1n+p, lt_succ(p))),
    gcd_mul.go(1n+p, qq, x, p, lt_succ(p)))

# Coprimality
# -----------

law coprime_gcd:
  for +x: Nat
  for +p: Nat
  for cop: @k: Nat -> Dv(k, x) -> Dv(k, 1n+p) -> {k == 1n : Nat}
  for gd: Dv(N.Nat.gcd(x, 1n+p), x) & Dv(N.Nat.gcd(x, 1n+p), 1n+p)
  {N.Nat.gcd(x, 1n+p) == 1n : Nat}

def coprime_gcd(x, p, cop, gd):
  match gd:
    case (d1, d2):
      cop(N.Nat.gcd(x, 1n+p), d1, d2)

# P | x Q and x, P coprime give P | Q (P = 1 + p, Q = 1 + q).
law coprime_dvd:
  for +x: Nat
  for +p: Nat
  for +q: Nat
  for cop: @k: Nat -> Dv(k, x) -> Dv(k, 1n+p) -> {k == 1n : Nat}
  for h: Dv(1n+p, Nat.mul(x, 1n+q))
  Dv(1n+p, 1n+q)

def coprime_dvd(x, p, q, cop, h):
  %Equal.trans(Nat, N.Nat.gcd(Nat.mul(1n+q, x), Nat.mul(1n+q, 1n+p)), Nat.mul(1n+q, N.Nat.gcd(x, 1n+p)), 1n+q,
      gcd_mul(q, x, 1n+p),
      Equal.trans(Nat, Nat.mul(1n+q, N.Nat.gcd(x, 1n+p)), Nat.mul(1n+q, 1n), 1n+q,
        Equal.cong(Nat, Nat, z => Nat.mul(1n+q, z), N.Nat.gcd(x, 1n+p), 1n, coprime_gcd(x, p, cop, gcd_dvd(x, 1n+p))),
        PN.mul_one_r(1n+q)))
    : Dv(1n+p, _)
  gcd_greatest(1n+p, Nat.mul(1n+q, x), Nat.mul(1n+q, 1n+p),
    (%PN.mul_comm(x, 1n+q) : Dv(1n+p, _)
     h),
    (1n+q, PN.mul_comm(1n+q, 1n+p)))

law dv_antisym.go:
  for +p: Nat
  for +q: Nat
  for +s: Nat
  for +t: Nat
  for +e1: {1n+q == Nat.mul(1n+p, s) : Nat}
  for +e2: {1n+p == Nat.mul(1n+q, t) : Nat}
  {1n+p == 1n+q : Nat}

def dv_antisym.go(p, q, s, t, e1, e2):
  %Equal.sym(Nat, 1n+q, Nat.mul(1n+p, s), e1) : {1n+p == _ : Nat}
  %Equal.sym(Nat, s, 1n,
      mul_eq_one(s, t, mul_cancel_r(p, Nat.mul(s, t), 1n,
        (%Equal.sym(Nat, Nat.add(1n+p, 0n), 1n+p, PN.add_zero_r(1n+p)) : {Nat.mul(Nat.mul(s, t), 1n+p) == _ : Nat}
         %Equal.sym(Nat, 1n+p, Nat.mul(1n+q, t), e2) : {Nat.mul(Nat.mul(s, t), 1n+p) == _ : Nat}
         %Equal.sym(Nat, 1n+q, Nat.mul(1n+p, s), e1) : {Nat.mul(Nat.mul(s, t), 1n+p) == Nat.mul(_, t) : Nat}
         R.Ring.eq(
           R.EMul{R.EMul{R.EVar{0n}, R.EVar{1n}}, R.EAdd{R.ENum{1n}, R.EVar{2n}}},
           R.EMul{R.EMul{R.EAdd{R.ENum{1n}, R.EVar{2n}}, R.EVar{0n}}, R.EVar{1n}},
           [s, t, p], {==})))))
    : {1n+p == Nat.mul(1n+p, _) : Nat}
  Equal.sym(Nat, Nat.mul(1n+p, 1n), 1n+p, PN.mul_one_r(1n+p))

law dv_antisym:
  for +p: Nat
  for +q: Nat
  for h1: Dv(1n+p, 1n+q)
  for h2: Dv(1n+q, 1n+p)
  {1n+p == 1n+q : Nat}

def dv_antisym(p, q, h1, h2):
  match h1:
    case (s, e1):
      match h2:
        case (t, e2):
          dv_antisym.go(p, q, s, t, e1, e2)
