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
