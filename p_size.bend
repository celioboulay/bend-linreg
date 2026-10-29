import Base
import ./num.bend as N
import ./p_nat.bend as PN
import ./p_ring.bend as R
import ./p_int.bend as PI
import ./p_div.bend as PD
import ./p_rat.bend as PR
import ./LAWS.bend as Laws
import ./linreg.bend as L

# The size checks. linreg.bend's capped arithmetic computes sat(x) =
# min(x, K + 1) of the exact value x, so each check it makes is the exact
# condition LAWS.bend states. K stays symbolic throughout: the checker
# counts in unary, so a proof that evaluated 2^47 would never finish.

# Order
# -----

law le_refl:
  for +x: Nat
  {Nat.is_le(x, x) == True{} : Bool}

def le_refl(x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      le_refl(p)

law le_succ_false:
  for +k: Nat
  {Nat.is_le(1n+k, k) == False{} : Bool}

def le_succ_false(k):
  match k:
    case 0n:
      {==}
    case 1n+p:
      le_succ_false(p)

# 1 + y + c > y
law gt_plus:
  for +y: Nat
  for +c: Nat
  {Nat.is_le(1n+Nat.add(y, c), y) == False{} : Bool}

def gt_plus(y, c):
  match y:
    case 0n:
      {==}
    case 1n+p:
      gt_plus(p, c)

law le_w_refl:
  for +x: Nat
  PD.LeW(x, x)

def le_w_refl(x):
  (0n, Equal.sym(Nat, Nat.add(x, 0n), x, PN.add_zero_r(x)))

law le_of_w:
  for +x: Nat
  for +y: Nat
  for w: PD.LeW(x, y)
  {Nat.is_le(x, y) == True{} : Bool}

def le_of_w(x, y, w):
  match w:
    case (+k, e):
      %Equal.sym(Nat, y, Nat.add(x, k), e) : {Nat.is_le(x, _) == True{} : Bool}
      PD.le_plus(x, k)

law gt_of_w:
  for +x: Nat
  for +y: Nat
  for w: PD.LeW(1n+y, x)
  {Nat.is_le(x, y) == False{} : Bool}

def gt_of_w(x, y, w):
  match w:
    case (+c, e):
      %Equal.sym(Nat, x, Nat.add(1n+y, c), e) : {Nat.is_le(_, y) == False{} : Bool}
      gt_plus(y, c)

# x > y as a gap: x == 1 + y + c
law le_false_w:
  for +x: Nat
  for +y: Nat
  for h: {Nat.is_le(x, y) == False{} : Bool}
  PD.LeW(1n+y, x)

def le_false_w(x, y, h):
  match x y:
    case 0n _:
      Empty.absurd(PD.LeW(1n+y, 0n),
        PD.Bool.ft(Equal.trans(Bool, False{}, Nat.is_le(0n, y), True{}, Equal.sym(Bool, Nat.is_le(0n, y), False{}, h), PD.le_zero_l(y))))
    case 1n+p 0n:
      (p, {==})
    case 1n+p 1n+q:
      PD.le_witness.succ(1n+q, p, le_false_w(p, q, h))

law le_iff.go:
  for +p: Nat
  for +q: Nat
  for +p2: Nat
  for +q2: Nat
  for b: Bool
  for e: {Nat.is_le(p, q) == b : Bool}
  for f: PD.LeW(p, q) -> PD.LeW(p2, q2)
  for g: PD.LeW(1n+q, p) -> PD.LeW(1n+q2, p2)
  {b == Nat.is_le(p2, q2) : Bool}

def le_iff.go(p, q, p2, q2, b, e, f, g):
  match b:
    case True{}:
      Equal.sym(Bool, Nat.is_le(p2, q2), True{}, le_of_w(p2, q2, f(PD.le_witness(p, q, e))))
    case False{}:
      Equal.sym(Bool, Nat.is_le(p2, q2), False{}, gt_of_w(p2, q2, g(le_false_w(p, q, e))))

# Two comparisons that hold together and fail together agree.
law le_iff:
  for +p: Nat
  for +q: Nat
  for +p2: Nat
  for +q2: Nat
  for f: PD.LeW(p, q) -> PD.LeW(p2, q2)
  for g: PD.LeW(1n+q, p) -> PD.LeW(1n+q2, p2)
  {Nat.is_le(p, q) == Nat.is_le(p2, q2) : Bool}

def le_iff(p, q, p2, q2, f, g):
  le_iff.go(p, q, p2, q2, Nat.is_le(p, q), {==}, f, g)

law le_succ_r:
  for +x: Nat
  for +k: Nat
  for h: {Nat.is_le(x, k) == True{} : Bool}
  {Nat.is_le(x, 1n+k) == True{} : Bool}

def le_succ_r(x, k, h):
  match x k:
    case 0n _:
      {==}
    case 1n+p 0n:
      Empty.absurd({Nat.is_le(1n+p, 1n) == True{} : Bool}, PD.Bool.ft(h))
    case 1n+p 1n+j:
      le_succ_r(p, j, h)

# Bool
# ----

law and_tt:
  for a: Bool
  for b: Bool
  for ea: {a == True{} : Bool}
  for eb: {b == True{} : Bool}
  {Bool.and(a, b) == True{} : Bool}

def and_tt(a, b, ea, eb):
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

law and_f_l:
  for a: Bool
  for b: Bool
  for ea: {a == False{} : Bool}
  {Bool.and(a, b) == False{} : Bool}

def and_f_l(a, b, ea):
  %Equal.sym(Bool, a, False{}, ea) : {Bool.and(_, b) == False{} : Bool}
  {==}

law and_f_r:
  for a: Bool
  for b: Bool
  for eb: {b == False{} : Bool}
  {Bool.and(a, b) == False{} : Bool}

def and_f_r(a, b, eb):
  match a:
    case True{}:
      eb
    case False{}:
      {==}

law and_t_l:
  for a: Bool
  for b: Bool
  for h: {Bool.and(a, b) == True{} : Bool}
  {a == True{} : Bool}

def and_t_l(a, b, h):
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, PD.Bool.ft(h))

law and_t_r:
  for a: Bool
  for b: Bool
  for h: {Bool.and(a, b) == True{} : Bool}
  {b == True{} : Bool}

def and_t_r(a, b, h):
  match a:
    case True{}:
      h
    case False{}:
      Empty.absurd({b == True{} : Bool}, PD.Bool.ft(h))

law and_true_r:
  for a: Bool
  {Bool.and(a, True{}) == a : Bool}

def and_true_r(a):
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# Max
# ---

law max_r:
  for +x: Nat
  for +y: Nat
  for h: {Nat.is_le(x, y) == True{} : Bool}
  {Nat.max(x, y) == y : Nat}

def max_r(x, y, h):
  match x y:
    case 0n _:
      {==}
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, PD.Bool.ft(h))
    case 1n+p 1n+q:
      %max_r(p, q, h) : {1n+Nat.max(p, q) == 1n+_ : Nat}
      {==}

law max_l:
  for +x: Nat
  for +y: Nat
  for h: {Nat.is_le(y, x) == True{} : Bool}
  {Nat.max(x, y) == x : Nat}

def max_l(x, y, h):
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({Nat.max(0n, 1n+q) == 0n : Nat}, PD.Bool.ft(h))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      %max_l(p, q, h) : {1n+Nat.max(p, q) == 1n+_ : Nat}
      {==}

# max(a, b) <= k exactly when a <= k and b <= k
law ok_max:
  for +k: Nat
  for +a: Nat
  for +b: Nat
  {Nat.is_le(Nat.max(a, b), k) == Bool.and(Nat.is_le(a, k), Nat.is_le(b, k)) : Bool}

def ok_max(k, a, b):
  match k a b:
    case 0n 0n _:
      {==}
    case 1n+j 0n _:
      {==}
    case 0n 1n+p 0n:
      {==}
    case 0n 1n+p 1n+q:
      {==}
    case 1n+j 1n+p 0n:
      Equal.sym(Bool, Bool.and(Nat.is_le(p, j), True{}), Nat.is_le(p, j), and_true_r(Nat.is_le(p, j)))
    case 1n+j 1n+p 1n+q:
      ok_max(j, p, q)

law max_cong:
  for +a1: Nat
  for +b1: Nat
  for +a2: Nat
  for +b2: Nat
  for e1: {a1 == b1 : Nat}
  for e2: {a2 == b2 : Nat}
  {Nat.max(a1, a2) == Nat.max(b1, b2) : Nat}

def max_cong(a1, b1, a2, b2, e1, e2):
  %e1 : {Nat.max(a1, a2) == Nat.max(_, b2) : Nat}
  %e2 : {Nat.max(a1, a2) == Nat.max(a1, _) : Nat}
  {==}

# Division
# --------

law le_div.f:
  for +k: Nat
  for +ap: Nat
  for +b: Nat
  for w: PD.LeW(b, Nat.div(k, 1n+ap))
  PD.LeW(Nat.mul(1n+ap, b), k)

def le_div.f(k, ap, b, w):
  match w:
    case (+c, e):
      (Nat.add(Nat.mul(c, 1n+ap), Nat.mod(k, 1n+ap)),
        (%PD.div_mod(k, ap) : {_ == Nat.add(Nat.mul(1n+ap, b), Nat.add(Nat.mul(c, 1n+ap), Nat.mod(k, 1n+ap))) : Nat}
         %Equal.sym(Nat, Nat.div(k, 1n+ap), Nat.add(b, c), e)
           : {Nat.add(Nat.mul(_, 1n+ap), Nat.mod(k, 1n+ap))
               == Nat.add(Nat.mul(1n+ap, b), Nat.add(Nat.mul(c, 1n+ap), Nat.mod(k, 1n+ap))) : Nat}
         R.Ring.eq(R.EAdd{R.EMul{R.EAdd{R.EVar{0n}, R.EVar{1n}}, R.EAdd{R.ENum{1n}, R.EVar{2n}}}, R.EVar{3n}}, R.EAdd{R.EMul{R.EAdd{R.ENum{1n}, R.EVar{2n}}, R.EVar{0n}}, R.EAdd{R.EMul{R.EVar{1n}, R.EAdd{R.ENum{1n}, R.EVar{2n}}}, R.EVar{3n}}}, [b, c, ap, Nat.mod(k, 1n+ap)], {==})))

law le_div.g2:
  for +k: Nat
  for +ap: Nat
  for +b: Nat
  for +c: Nat
  for e: {b == Nat.add(1n+Nat.div(k, 1n+ap), c) : Nat}
  for ws: PD.LeW(Nat.mod(k, 1n+ap), ap)
  PD.LeW(1n+k, Nat.mul(1n+ap, b))

def le_div.g2(k, ap, b, c, e, ws):
  match ws:
    case (+s, es):
      (Nat.add(s, Nat.mul(1n+ap, c)),
        (%Equal.sym(Nat, b, Nat.add(1n+Nat.div(k, 1n+ap), c), e)
           : {Nat.mul(1n+ap, _) == Nat.add(1n+k, Nat.add(s, Nat.mul(1n+ap, c))) : Nat}
         %PD.div_mod(k, ap)
           : {Nat.mul(1n+ap, Nat.add(1n+Nat.div(k, 1n+ap), c)) == Nat.add(1n+_, Nat.add(s, Nat.mul(1n+ap, c))) : Nat}
         %Equal.sym(Nat, ap, Nat.add(Nat.mod(k, 1n+ap), s), es)
           : {Nat.mul(1n+_, Nat.add(1n+Nat.div(k, 1n+ap), c))
               == Nat.add(1n+Nat.add(Nat.mul(Nat.div(k, 1n+ap), 1n+_), Nat.mod(k, 1n+ap)), Nat.add(s, Nat.mul(1n+_, c))) : Nat}
         R.Ring.eq(R.EMul{R.EAdd{R.ENum{1n}, R.EAdd{R.EVar{2n}, R.EVar{3n}}}, R.EAdd{R.EAdd{R.ENum{1n}, R.EVar{0n}}, R.EVar{1n}}}, R.EAdd{R.EAdd{R.ENum{1n}, R.EAdd{R.EMul{R.EVar{0n}, R.EAdd{R.ENum{1n}, R.EAdd{R.EVar{2n}, R.EVar{3n}}}}, R.EVar{2n}}}, R.EAdd{R.EVar{3n}, R.EMul{R.EAdd{R.ENum{1n}, R.EAdd{R.EVar{2n}, R.EVar{3n}}}, R.EVar{1n}}}}, [Nat.div(k, 1n+ap), c, Nat.mod(k, 1n+ap), s], {==})))

law le_div.g:
  for +k: Nat
  for +ap: Nat
  for +b: Nat
  for w: PD.LeW(1n+Nat.div(k, 1n+ap), b)
  PD.LeW(1n+k, Nat.mul(1n+ap, b))

def le_div.g(k, ap, b, w):
  match w:
    case (+c, e):
      le_div.g2(k, ap, b, c, e, PD.le_witness(Nat.mod(k, 1n+ap), ap, PD.mod_le(k, ap)))

# b <= k / a exactly when a b <= k
law le_div:
  for +k: Nat
  for +ap: Nat
  for +b: Nat
  {Nat.is_le(b, Nat.div(k, 1n+ap)) == Nat.is_le(Nat.mul(1n+ap, b), k) : Bool}

def le_div(k, ap, b):
  le_iff(b, Nat.div(k, 1n+ap), Nat.mul(1n+ap, b), k, w => le_div.f(k, ap, b, w), w => le_div.g(k, ap, b, w))

# Saturation
# ----------

def sat.go(ok: Bool, +k: Nat, +x: Nat) -> Nat:
  match ok:
    case True{}:
      x
    case False{}:
      1n+k

# min(x, k + 1)
def sat(+k: Nat, +x: Nat) -> Nat:
  sat.go(Nat.is_le(x, k), k, x)

law sat_le:
  for +k: Nat
  for +x: Nat
  for h: {Nat.is_le(x, k) == True{} : Bool}
  {sat(k, x) == x : Nat}

def sat_le(k, x, h):
  %Equal.sym(Bool, Nat.is_le(x, k), True{}, h) : {sat.go(_, k, x) == x : Nat}
  {==}

law sat_gt:
  for +k: Nat
  for +x: Nat
  for h: {Nat.is_le(x, k) == False{} : Bool}
  {sat(k, x) == 1n+k : Nat}

def sat_gt(k, x, h):
  %Equal.sym(Bool, Nat.is_le(x, k), False{}, h) : {sat.go(_, k, x) == 1n+k : Nat}
  {==}

law sat_zero:
  for +k: Nat
  {sat(k, 0n) == 0n : Nat}

def sat_zero(k):
  sat_le(k, 0n, PD.le_zero_l(k))

law sat_cong:
  for +k: Nat
  for +a: Nat
  for +b: Nat
  for e: {a == b : Nat}
  {sat(k, a) == sat(k, b) : Nat}

def sat_cong(k, a, b, e):
  Equal.cong(Nat, Nat, z => sat(k, z), a, b, e)

law ok_sat.go:
  for +k: Nat
  for +x: Nat
  for b: Bool
  for e: {Nat.is_le(x, k) == b : Bool}
  {Nat.is_le(sat.go(b, k, x), k) == b : Bool}

def ok_sat.go(k, x, b, e):
  match b:
    case True{}:
      e
    case False{}:
      le_succ_false(k)

# checking sat(x) <= k checks x <= k
law ok_sat:
  for +k: Nat
  for +x: Nat
  {Nat.is_le(sat(k, x), k) == Nat.is_le(x, k) : Bool}

def ok_sat(k, x):
  ok_sat.go(k, x, Nat.is_le(x, k), {==})

# x > k gives x (1 + y) > k
law big_mul:
  for +k: Nat
  for +x: Nat
  for +y: Nat
  for w: PD.LeW(1n+k, x)
  {Nat.is_le(Nat.mul(x, 1n+y), k) == False{} : Bool}

def big_mul(k, x, y, w):
  match w:
    case (+c, e):
      gt_of_w(Nat.mul(x, 1n+y), k, (Nat.add(c, Nat.mul(x, y)),
        (%Equal.sym(Nat, x, Nat.add(1n+k, c), e)
           : {Nat.mul(_, 1n+y) == Nat.add(1n+k, Nat.add(c, Nat.mul(_, y))) : Nat}
         R.Ring.eq(R.EMul{R.EAdd{R.EAdd{R.ENum{1n}, R.EVar{0n}}, R.EVar{1n}}, R.EAdd{R.ENum{1n}, R.EVar{2n}}}, R.EAdd{R.EAdd{R.ENum{1n}, R.EVar{0n}}, R.EAdd{R.EVar{1n}, R.EMul{R.EAdd{R.EAdd{R.ENum{1n}, R.EVar{0n}}, R.EVar{1n}}, R.EVar{2n}}}}, [k, c, y], {==}))))

law sat_mul_l.go:
  for +k: Nat
  for +x: Nat
  for b: Bool
  for e: {Nat.is_le(x, k) == b : Bool}
  for +y: Nat
  {sat(k, Nat.mul(sat.go(b, k, x), y)) == sat(k, Nat.mul(x, y)) : Nat}

def sat_mul_l.go(k, x, b, e, y):
  match b y:
    case True{} _:
      {==}
    case False{} 0n:
      %Equal.sym(Nat, Nat.mul(k, 0n), 0n, PN.mul_zero_r(k)) : {sat(k, _) == sat(k, Nat.mul(x, 0n)) : Nat}
      %Equal.sym(Nat, Nat.mul(x, 0n), 0n, PN.mul_zero_r(x)) : {sat(k, 0n) == sat(k, _) : Nat}
      {==}
    case False{} 1n+yp:
      Equal.trans(Nat, sat(k, Nat.mul(1n+k, 1n+yp)), 1n+k, sat(k, Nat.mul(x, 1n+yp)),
        sat_gt(k, Nat.mul(1n+k, 1n+yp), big_mul(k, 1n+k, yp, le_w_refl(1n+k))),
        Equal.sym(Nat, sat(k, Nat.mul(x, 1n+yp)), 1n+k,
          sat_gt(k, Nat.mul(x, 1n+yp), big_mul(k, x, yp, le_false_w(x, k, e)))))

law sat_mul_l:
  for +k: Nat
  for +x: Nat
  for +y: Nat
  {sat(k, Nat.mul(sat(k, x), y)) == sat(k, Nat.mul(x, y)) : Nat}

def sat_mul_l(k, x, y):
  sat_mul_l.go(k, x, Nat.is_le(x, k), {==}, y)

law sat_mul_r:
  for +k: Nat
  for +x: Nat
  for +y: Nat
  {sat(k, Nat.mul(x, sat(k, y))) == sat(k, Nat.mul(x, y)) : Nat}

def sat_mul_r(k, x, y):
  %PN.mul_comm(sat(k, y), x) : {sat(k, _) == sat(k, Nat.mul(x, y)) : Nat}
  %PN.mul_comm(y, x) : {sat(k, Nat.mul(sat(k, y), x)) == sat(k, _) : Nat}
  sat_mul_l(k, y, x)

law sat_mul:
  for +k: Nat
  for +x: Nat
  for +y: Nat
  {sat(k, Nat.mul(sat(k, x), sat(k, y))) == sat(k, Nat.mul(x, y)) : Nat}

def sat_mul(k, x, y):
  Equal.trans(Nat, sat(k, Nat.mul(sat(k, x), sat(k, y))), sat(k, Nat.mul(x, sat(k, y))), sat(k, Nat.mul(x, y)),
    sat_mul_l(k, x, sat(k, y)), sat_mul_r(k, x, y))

law sat_add_l.w:
  for +k: Nat
  for +x: Nat
  for +y: Nat
  for w: PD.LeW(1n+k, x)
  PD.LeW(1n+k, Nat.add(x, y))

def sat_add_l.w(k, x, y, w):
  match w:
    case (+c, e):
      (Nat.add(c, y),
        (%Equal.sym(Nat, x, Nat.add(1n+k, c), e) : {Nat.add(_, y) == Nat.add(1n+k, Nat.add(c, y)) : Nat}
         PN.add_assoc(1n+k, c, y)))

law sat_add_l.go:
  for +k: Nat
  for +x: Nat
  for +y: Nat
  for b: Bool
  for e: {Nat.is_le(x, k) == b : Bool}
  {sat(k, Nat.add(sat.go(b, k, x), y)) == sat(k, Nat.add(x, y)) : Nat}

def sat_add_l.go(k, x, y, b, e):
  match b:
    case True{}:
      {==}
    case False{}:
      Equal.trans(Nat, sat(k, Nat.add(1n+k, y)), 1n+k, sat(k, Nat.add(x, y)),
        sat_gt(k, Nat.add(1n+k, y), gt_plus(k, y)),
        Equal.sym(Nat, sat(k, Nat.add(x, y)), 1n+k,
          sat_gt(k, Nat.add(x, y), gt_of_w(Nat.add(x, y), k, sat_add_l.w(k, x, y, le_false_w(x, k, e))))))

law sat_add_l:
  for +k: Nat
  for +x: Nat
  for +y: Nat
  {sat(k, Nat.add(sat(k, x), y)) == sat(k, Nat.add(x, y)) : Nat}

def sat_add_l(k, x, y):
  sat_add_l.go(k, x, y, Nat.is_le(x, k), {==})

law sat_max.go:
  for +k: Nat
  for +x: Nat
  for +y: Nat
  for bx: Bool
  for ex: {Nat.is_le(x, k) == bx : Bool}
  for by: Bool
  for ey: {Nat.is_le(y, k) == by : Bool}
  {Nat.max(sat.go(bx, k, x), sat.go(by, k, y)) == sat(k, Nat.max(x, y)) : Nat}

def sat_max.go(k, x, y, bx, ex, by, ey):
  match bx by:
    case True{} True{}:
      Equal.sym(Nat, sat(k, Nat.max(x, y)), Nat.max(x, y),
        sat_le(k, Nat.max(x, y),
          Equal.trans(Bool, Nat.is_le(Nat.max(x, y), k), Bool.and(Nat.is_le(x, k), Nat.is_le(y, k)), True{},
            ok_max(k, x, y), and_tt(Nat.is_le(x, k), Nat.is_le(y, k), ex, ey))))
    case True{} False{}:
      Equal.trans(Nat, Nat.max(x, 1n+k), 1n+k, sat(k, Nat.max(x, y)),
        max_r(x, 1n+k, le_succ_r(x, k, ex)),
        Equal.sym(Nat, sat(k, Nat.max(x, y)), 1n+k,
          sat_gt(k, Nat.max(x, y),
            Equal.trans(Bool, Nat.is_le(Nat.max(x, y), k), Bool.and(Nat.is_le(x, k), Nat.is_le(y, k)), False{},
              ok_max(k, x, y), and_f_r(Nat.is_le(x, k), Nat.is_le(y, k), ey)))))
    case False{} True{}:
      Equal.trans(Nat, Nat.max(1n+k, y), 1n+k, sat(k, Nat.max(x, y)),
        max_l(1n+k, y, le_succ_r(y, k, ey)),
        Equal.sym(Nat, sat(k, Nat.max(x, y)), 1n+k,
          sat_gt(k, Nat.max(x, y),
            Equal.trans(Bool, Nat.is_le(Nat.max(x, y), k), Bool.and(Nat.is_le(x, k), Nat.is_le(y, k)), False{},
              ok_max(k, x, y), and_f_l(Nat.is_le(x, k), Nat.is_le(y, k), ex)))))
    case False{} False{}:
      Equal.trans(Nat, Nat.max(1n+k, 1n+k), 1n+k, sat(k, Nat.max(x, y)),
        max_l(1n+k, 1n+k, le_refl(1n+k)),
        Equal.sym(Nat, sat(k, Nat.max(x, y)), 1n+k,
          sat_gt(k, Nat.max(x, y),
            Equal.trans(Bool, Nat.is_le(Nat.max(x, y), k), Bool.and(Nat.is_le(x, k), Nat.is_le(y, k)), False{},
              ok_max(k, x, y), and_f_l(Nat.is_le(x, k), Nat.is_le(y, k), ex)))))

law sat_max:
  for +k: Nat
  for +x: Nat
  for +y: Nat
  {Nat.max(sat(k, x), sat(k, y)) == sat(k, Nat.max(x, y)) : Nat}

def sat_max(k, x, y):
  sat_max.go(k, x, y, Nat.is_le(x, k), {==}, Nat.is_le(y, k), {==})

# The code's capped operations
# ----------------------------

law mul_go:
  for +k: Nat
  for c: Bool
  for +a: Nat
  for +b: Nat
  {L.Limit.mul.go(k, c, a, b) == sat.go(c, k, Nat.mul(a, b)) : Nat}

def mul_go(k, c, a, b):
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

law limit_mul:
  for +k: Nat
  for +a: Nat
  for +b: Nat
  {L.Limit.mul(k, a, b) == sat(k, Nat.mul(a, b)) : Nat}

def limit_mul(k, a, b):
  match a:
    case 0n:
      Equal.sym(Nat, sat(k, 0n), 0n, sat_zero(k))
    case 1n+p:
      %Equal.sym(Bool, Nat.is_le(b, Nat.div(k, 1n+p)), Nat.is_le(Nat.mul(1n+p, b), k), le_div(k, p, b))
        : {L.Limit.mul.go(k, _, 1n+p, b) == sat(k, Nat.mul(1n+p, b)) : Nat}
      mul_go(k, Nat.is_le(Nat.mul(1n+p, b), k), 1n+p, b)

# Limit.mul of two capped values
law lm:
  for +k: Nat
  for +x: Nat
  for +y: Nat
  {L.Limit.mul(k, sat(k, x), sat(k, y)) == sat(k, Nat.mul(x, y)) : Nat}

def lm(k, x, y):
  Equal.trans(Nat, L.Limit.mul(k, sat(k, x), sat(k, y)), sat(k, Nat.mul(sat(k, x), sat(k, y))), sat(k, Nat.mul(x, y)),
    limit_mul(k, sat(k, x), sat(k, y)), sat_mul(k, x, y))

law add_go:
  for +k: Nat
  for c: Bool
  for +a: Nat
  for +b: Nat
  {L.Limit.add.go(k, c, a, b) == sat.go(c, k, Nat.add(a, b)) : Nat}

def add_go(k, c, a, b):
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

law sub_add_cancel:
  for +b: Nat
  for +c: Nat
  {Nat.sub(Nat.add(b, c), b) == c : Nat}

def sub_add_cancel(b, c):
  match b:
    case 0n:
      PI.Nat.sub_zero_r(c)
    case 1n+p:
      sub_add_cancel(p, c)

law sub_succ_self:
  for +k: Nat
  {Nat.sub(k, 1n+k) == 0n : Nat}

def sub_succ_self(k):
  match k:
    case 0n:
      {==}
    case 1n+p:
      sub_succ_self(p)

law le_sub.f:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for w: PD.LeW(a, c)
  PD.LeW(Nat.add(a, b), Nat.add(b, c))

def le_sub.f(a, b, c, w):
  match w:
    case (+v, e):
      (v, (%Equal.sym(Nat, c, Nat.add(a, v), e) : {Nat.add(b, _) == Nat.add(Nat.add(a, b), v) : Nat}
           R.Ring.eq(R.EAdd{R.EVar{1n}, R.EAdd{R.EVar{0n}, R.EVar{2n}}}, R.EAdd{R.EAdd{R.EVar{0n}, R.EVar{1n}}, R.EVar{2n}}, [a, b, v], {==})))

law le_sub.g:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for w: PD.LeW(1n+c, a)
  PD.LeW(1n+Nat.add(b, c), Nat.add(a, b))

def le_sub.g(a, b, c, w):
  match w:
    case (+v, e):
      (v, (%Equal.sym(Nat, a, Nat.add(1n+c, v), e) : {Nat.add(_, b) == Nat.add(1n+Nat.add(b, c), v) : Nat}
           R.Ring.eq(R.EAdd{R.EAdd{R.EAdd{R.ENum{1n}, R.EVar{1n}}, R.EVar{2n}}, R.EVar{0n}}, R.EAdd{R.EAdd{R.ENum{1n}, R.EAdd{R.EVar{0n}, R.EVar{1n}}}, R.EVar{2n}}, [b, c, v], {==})))

law le_sub.go:
  for +k: Nat
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for e: {k == Nat.add(b, c) : Nat}
  {Nat.is_le(a, Nat.sub(k, b)) == Nat.is_le(Nat.add(a, b), k) : Bool}

def le_sub.go(k, a, b, c, e):
  %Equal.sym(Nat, k, Nat.add(b, c), e) : {Nat.is_le(a, Nat.sub(_, b)) == Nat.is_le(Nat.add(a, b), _) : Bool}
  %Equal.sym(Nat, Nat.sub(Nat.add(b, c), b), c, sub_add_cancel(b, c))
    : {Nat.is_le(a, _) == Nat.is_le(Nat.add(a, b), Nat.add(b, c)) : Bool}
  le_iff(a, c, Nat.add(a, b), Nat.add(b, c), w => le_sub.f(a, b, c, w), w => le_sub.g(a, b, c, w))

law le_sub.w:
  for +k: Nat
  for +a: Nat
  for +b: Nat
  for w: PD.LeW(b, k)
  {Nat.is_le(a, Nat.sub(k, b)) == Nat.is_le(Nat.add(a, b), k) : Bool}

def le_sub.w(k, a, b, w):
  match w:
    case (+c, e):
      le_sub.go(k, a, b, c, e)

# a <= k - b exactly when a + b <= k, for b <= k
law le_sub:
  for +k: Nat
  for +a: Nat
  for +b: Nat
  for h: {Nat.is_le(b, k) == True{} : Bool}
  {Nat.is_le(a, Nat.sub(k, b)) == Nat.is_le(Nat.add(a, b), k) : Bool}

def le_sub(k, a, b, h):
  le_sub.w(k, a, b, PD.le_witness(b, k, h))

law gt_add_l:
  for +k: Nat
  for +a: Nat
  for +y: Nat
  for w: PD.LeW(1n+k, y)
  PD.LeW(1n+k, Nat.add(a, y))

def gt_add_l(k, a, y, w):
  match w:
    case (+c, e):
      (Nat.add(a, c), (%Equal.sym(Nat, y, Nat.add(1n+k, c), e) : {Nat.add(a, _) == Nat.add(1n+k, Nat.add(a, c)) : Nat}
                       R.Ring.eq(R.EAdd{R.EVar{0n}, R.EAdd{R.EAdd{R.ENum{1n}, R.EVar{1n}}, R.EVar{2n}}}, R.EAdd{R.EAdd{R.ENum{1n}, R.EVar{1n}}, R.EAdd{R.EVar{0n}, R.EVar{2n}}}, [a, k, c], {==})))

law limit_add_sat.go:
  for +k: Nat
  for +y: Nat
  for by: Bool
  for ey: {Nat.is_le(y, k) == by : Bool}
  for +a: Nat
  {L.Limit.add(k, a, sat.go(by, k, y)) == sat(k, Nat.add(a, y)) : Nat}

def limit_add_sat.go(k, y, by, ey, a):
  match by a:
    case True{} _:
      %Equal.sym(Bool, Nat.is_le(a, Nat.sub(k, y)), Nat.is_le(Nat.add(a, y), k), le_sub(k, a, y, ey))
        : {L.Limit.add.go(k, _, a, y) == sat(k, Nat.add(a, y)) : Nat}
      add_go(k, Nat.is_le(Nat.add(a, y), k), a, y)
    case False{} 0n:
      %Equal.sym(Nat, Nat.sub(k, 1n+k), 0n, sub_succ_self(k)) : {L.Limit.add.go(k, Nat.is_le(0n, _), 0n, 1n+k) == sat(k, y) : Nat}
      Equal.sym(Nat, sat(k, y), 1n+k, sat_gt(k, y, ey))
    case False{} 1n+ap:
      %Equal.sym(Nat, Nat.sub(k, 1n+k), 0n, sub_succ_self(k))
        : {L.Limit.add.go(k, Nat.is_le(1n+ap, _), 1n+ap, 1n+k) == sat(k, Nat.add(1n+ap, y)) : Nat}
      Equal.sym(Nat, sat(k, Nat.add(1n+ap, y)), 1n+k,
        sat_gt(k, Nat.add(1n+ap, y), gt_of_w(Nat.add(1n+ap, y), k, gt_add_l(k, 1n+ap, y, le_false_w(y, k, ey)))))

law limit_add_sat:
  for +k: Nat
  for +a: Nat
  for +y: Nat
  {L.Limit.add(k, a, sat(k, y)) == sat(k, Nat.add(a, y)) : Nat}

def limit_add_sat(k, a, y):
  limit_add_sat.go(k, y, Nat.is_le(y, k), {==}, a)

# Limit.add of two capped values
law limit_add:
  for +k: Nat
  for +x: Nat
  for +y: Nat
  {L.Limit.add(k, sat(k, x), sat(k, y)) == sat(k, Nat.add(x, y)) : Nat}

def limit_add(k, x, y):
  Equal.trans(Nat, L.Limit.add(k, sat(k, x), sat(k, y)), sat(k, Nat.add(sat(k, x), y)), sat(k, Nat.add(x, y)),
    limit_add_sat(k, sat(k, x), y), sat_add_l(k, x, y))

law lmul_cong:
  for +k: Nat
  for +a1: Nat
  for +b1: Nat
  for +a2: Nat
  for +b2: Nat
  for e1: {a1 == b1 : Nat}
  for e2: {a2 == b2 : Nat}
  {L.Limit.mul(k, a1, a2) == L.Limit.mul(k, b1, b2) : Nat}

def lmul_cong(k, a1, b1, a2, b2, e1, e2):
  %e1 : {L.Limit.mul(k, a1, a2) == L.Limit.mul(k, _, b2) : Nat}
  %e2 : {L.Limit.mul(k, a1, a2) == L.Limit.mul(k, a1, _) : Nat}
  {==}

# lcm
# ---

law le_w_trans:
  for +x: Nat
  for +y: Nat
  for +z: Nat
  for w1: PD.LeW(x, y)
  for w2: PD.LeW(y, z)
  PD.LeW(x, z)

def le_w_trans(x, y, z, w1, w2):
  match w1:
    case (+a, e1):
      match w2:
        case (+b, e2):
          (Nat.add(a, b),
            (%Equal.sym(Nat, z, Nat.add(y, b), e2) : {_ == Nat.add(x, Nat.add(a, b)) : Nat}
             %Equal.sym(Nat, y, Nat.add(x, a), e1) : {Nat.add(_, b) == Nat.add(x, Nat.add(a, b)) : Nat}
             PN.add_assoc(x, a, b)))

law lcm_split.z:
  for +a: Nat
  for +bp: Nat
  for e: Empty
  exs qa: Nat
  exs qb: Nat
  {Laws.lcm(a, 1n+bp) == Nat.mul(qa, 1n+bp) : Nat}
    & {N.Nat.lcm(a, 1n+bp) == Nat.mul(qa, 1n+bp) : Nat}
    & {Nat.mul(qa, 1n+bp) == Nat.mul(a, 1n+qb) : Nat}

def lcm_split.z(a, bp, e):
  match e:

law lcm_split.go:
  for +a: Nat
  for +bp: Nat
  for +g: Nat
  for +eg: {N.Nat.gcd(a, 1n+bp) == g : Nat}
  for +qa: Nat
  for +ea: {a == Nat.mul(g, qa) : Nat}
  for +qb: Nat
  for +eb: {1n+bp == Nat.mul(g, qb) : Nat}
  exs qa: Nat
  exs qb: Nat
  {Laws.lcm(a, 1n+bp) == Nat.mul(qa, 1n+bp) : Nat}
    & {N.Nat.lcm(a, 1n+bp) == Nat.mul(qa, 1n+bp) : Nat}
    & {Nat.mul(qa, 1n+bp) == Nat.mul(a, 1n+qb) : Nat}

def lcm_split.go(a, bp, g, eg, qa, ea, qb, eb):
  match g qb:
    case 0n _:
      lcm_split.z(a, bp, PD.succ_ne_zero(bp, eb))
    case 1n+gp 0n:
      lcm_split.z(a, bp, PD.succ_ne_zero(bp, Equal.trans(Nat, 1n+bp, Nat.mul(gp, 0n), 0n, eb, PN.mul_zero_r(gp))))
    case 1n+gp 1n+qbp:
      (qa, (qbp,
        ((%Equal.sym(Nat, N.Nat.gcd(a, 1n+bp), 1n+gp, eg) : {Nat.div(Nat.mul(a, 1n+bp), _) == Nat.mul(qa, 1n+bp) : Nat}
          %Equal.sym(Nat, a, Nat.mul(1n+gp, qa), ea) : {Nat.div(Nat.mul(_, 1n+bp), 1n+gp) == Nat.mul(qa, 1n+bp) : Nat}
          PR.div_of(Nat.mul(Nat.mul(1n+gp, qa), 1n+bp), gp, Nat.mul(qa, 1n+bp), PN.mul_assoc(1n+gp, qa, 1n+bp))),
         ((%Equal.sym(Nat, N.Nat.gcd(a, 1n+bp), 1n+gp, eg) : {Nat.mul(Nat.div(a, _), 1n+bp) == Nat.mul(qa, 1n+bp) : Nat}
           Equal.cong(Nat, Nat, z => Nat.mul(z, 1n+bp), Nat.div(a, 1n+gp), qa, PR.div_of(a, gp, qa, ea))),
          (%Equal.sym(Nat, 1n+bp, Nat.mul(1n+gp, 1n+qbp), eb) : {Nat.mul(qa, _) == Nat.mul(a, 1n+qbp) : Nat}
           %Equal.sym(Nat, a, Nat.mul(1n+gp, qa), ea) : {Nat.mul(qa, Nat.mul(1n+gp, 1n+qbp)) == Nat.mul(_, 1n+qbp) : Nat}
           R.Ring.eq(R.EMul{R.EVar{0n}, R.EMul{R.EAdd{R.ENum{1n}, R.EVar{1n}}, R.EAdd{R.ENum{1n}, R.EVar{2n}}}}, R.EMul{R.EMul{R.EAdd{R.ENum{1n}, R.EVar{1n}}, R.EVar{0n}}, R.EAdd{R.ENum{1n}, R.EVar{2n}}}, [qa, gp, qbp], {==}))))))

law lcm_split.h:
  for +a: Nat
  for +bp: Nat
  for da: PD.Dv(N.Nat.gcd(a, 1n+bp), a)
  for db: PD.Dv(N.Nat.gcd(a, 1n+bp), 1n+bp)
  exs qa: Nat
  exs qb: Nat
  {Laws.lcm(a, 1n+bp) == Nat.mul(qa, 1n+bp) : Nat}
    & {N.Nat.lcm(a, 1n+bp) == Nat.mul(qa, 1n+bp) : Nat}
    & {Nat.mul(qa, 1n+bp) == Nat.mul(a, 1n+qb) : Nat}

def lcm_split.h(a, bp, da, db):
  match da:
    case (+qa, ea):
      match db:
        case (+qb, eb):
          lcm_split.go(a, bp, N.Nat.gcd(a, 1n+bp), {==}, qa, ea, qb, eb)

law lcm_split.d:
  for +a: Nat
  for +bp: Nat
  for d: PD.Dv(N.Nat.gcd(a, 1n+bp), a) & PD.Dv(N.Nat.gcd(a, 1n+bp), 1n+bp)
  exs qa: Nat
  exs qb: Nat
  {Laws.lcm(a, 1n+bp) == Nat.mul(qa, 1n+bp) : Nat}
    & {N.Nat.lcm(a, 1n+bp) == Nat.mul(qa, 1n+bp) : Nat}
    & {Nat.mul(qa, 1n+bp) == Nat.mul(a, 1n+qb) : Nat}

def lcm_split.d(a, bp, d):
  match d:
    case (da, db):
      lcm_split.h(a, bp, da, db)

# lcm(a, b) = qa b = a (1 + qb), and the two lcm definitions agree
law lcm_split:
  for +a: Nat
  for +bp: Nat
  exs qa: Nat
  exs qb: Nat
  {Laws.lcm(a, 1n+bp) == Nat.mul(qa, 1n+bp) : Nat}
    & {N.Nat.lcm(a, 1n+bp) == Nat.mul(qa, 1n+bp) : Nat}
    & {Nat.mul(qa, 1n+bp) == Nat.mul(a, 1n+qb) : Nat}

def lcm_split(a, bp):
  lcm_split.d(a, bp, PD.gcd_dvd(a, 1n+bp))

law lcm_eq.go:
  for +a: Nat
  for +bp: Nat
  for s: &qa: Nat -> &qb: Nat ->
    {Laws.lcm(a, 1n+bp) == Nat.mul(qa, 1n+bp) : Nat}
    & {N.Nat.lcm(a, 1n+bp) == Nat.mul(qa, 1n+bp) : Nat}
    & {Nat.mul(qa, 1n+bp) == Nat.mul(a, 1n+qb) : Nat}
  {N.Nat.lcm(a, 1n+bp) == Laws.lcm(a, 1n+bp) : Nat}

def lcm_eq.go(a, bp, s):
  match s:
    case (+qa, (+qb, (p1, (p2, p3)))):
      Equal.trans(Nat, N.Nat.lcm(a, 1n+bp), Nat.mul(qa, 1n+bp), Laws.lcm(a, 1n+bp),
        p2, Equal.sym(Nat, Laws.lcm(a, 1n+bp), Nat.mul(qa, 1n+bp), p1))

law lcm_eq:
  for +a: Nat
  for +bp: Nat
  {N.Nat.lcm(a, 1n+bp) == Laws.lcm(a, 1n+bp) : Nat}

def lcm_eq(a, bp):
  lcm_eq.go(a, bp, lcm_split(a, bp))

law lcm_facts.mk:
  for +a: Nat
  for +bp: Nat
  for +qa: Nat
  for +qb: Nat
  for +p1: {Laws.lcm(a, 1n+bp) == Nat.mul(qa, 1n+bp) : Nat}
  for +p3: {Nat.mul(qa, 1n+bp) == Nat.mul(a, 1n+qb) : Nat}
  PD.Dv(a, Laws.lcm(a, 1n+bp)) & PD.Dv(1n+bp, Laws.lcm(a, 1n+bp)) & PD.LeW(a, Laws.lcm(a, 1n+bp))

def lcm_facts.mk(a, bp, qa, qb, p1, p3):
  ((1n+qb, Equal.trans(Nat, Laws.lcm(a, 1n+bp), Nat.mul(qa, 1n+bp), Nat.mul(a, 1n+qb), p1, p3)),
   ((qa, Equal.trans(Nat, Laws.lcm(a, 1n+bp), Nat.mul(qa, 1n+bp), Nat.mul(1n+bp, qa), p1, PN.mul_comm(qa, 1n+bp))),
    (Nat.mul(a, qb),
      Equal.trans(Nat, Laws.lcm(a, 1n+bp), Nat.mul(qa, 1n+bp), Nat.add(a, Nat.mul(a, qb)), p1,
        Equal.trans(Nat, Nat.mul(qa, 1n+bp), Nat.mul(a, 1n+qb), Nat.add(a, Nat.mul(a, qb)), p3, PN.mul_succ_r(a, qb))))))

law lcm_facts.go:
  for +a: Nat
  for +bp: Nat
  for s: &qa: Nat -> &qb: Nat ->
    {Laws.lcm(a, 1n+bp) == Nat.mul(qa, 1n+bp) : Nat}
    & {N.Nat.lcm(a, 1n+bp) == Nat.mul(qa, 1n+bp) : Nat}
    & {Nat.mul(qa, 1n+bp) == Nat.mul(a, 1n+qb) : Nat}
  PD.Dv(a, Laws.lcm(a, 1n+bp)) & PD.Dv(1n+bp, Laws.lcm(a, 1n+bp)) & PD.LeW(a, Laws.lcm(a, 1n+bp))

def lcm_facts.go(a, bp, s):
  match s:
    case (+qa, (+qb, (p1, (p2, p3)))):
      lcm_facts.mk(a, bp, qa, qb, p1, p3)

# a and b divide lcm(a, b), and lcm(a, b) >= a
law lcm_facts:
  for +a: Nat
  for +bp: Nat
  PD.Dv(a, Laws.lcm(a, 1n+bp)) & PD.Dv(1n+bp, Laws.lcm(a, 1n+bp)) & PD.LeW(a, Laws.lcm(a, 1n+bp))

def lcm_facts(a, bp):
  lcm_facts.go(a, bp, lcm_split(a, bp))

law lcm_ge.go:
  for +a: Nat
  for +bp: Nat
  for f: PD.Dv(a, Laws.lcm(a, 1n+bp)) & PD.Dv(1n+bp, Laws.lcm(a, 1n+bp)) & PD.LeW(a, Laws.lcm(a, 1n+bp))
  PD.LeW(a, Laws.lcm(a, 1n+bp))

def lcm_ge.go(a, bp, f):
  match f:
    case (da, (db, w)):
      w

law lcm_ge:
  for +a: Nat
  for +bp: Nat
  PD.LeW(a, Laws.lcm(a, 1n+bp))

def lcm_ge(a, bp):
  lcm_ge.go(a, bp, lcm_facts(a, bp))

# Limit.lcm is the capped lcm
law lcm_raw:
  for +k: Nat
  for +a: Nat
  for +bp: Nat
  {L.Limit.lcm(k, a, 1n+bp) == sat(k, Laws.lcm(a, 1n+bp)) : Nat}

def lcm_raw(k, a, bp):
  Equal.trans(Nat, L.Limit.lcm(k, a, 1n+bp), sat(k, N.Nat.lcm(a, 1n+bp)), sat(k, Laws.lcm(a, 1n+bp)),
    limit_mul(k, Nat.div(a, N.Nat.gcd(a, 1n+bp)), 1n+bp),
    sat_cong(k, N.Nat.lcm(a, 1n+bp), Laws.lcm(a, 1n+bp), lcm_eq(a, bp)))

law lcm_sat.go:
  for +k: Nat
  for +acc: Nat
  for b: Bool
  for e: {Nat.is_le(acc, k) == b : Bool}
  for +bp: Nat
  {sat(k, Laws.lcm(sat.go(b, k, acc), 1n+bp)) == sat(k, Laws.lcm(acc, 1n+bp)) : Nat}

def lcm_sat.go(k, acc, b, e, bp):
  match b:
    case True{}:
      {==}
    case False{}:
      Equal.trans(Nat, sat(k, Laws.lcm(1n+k, 1n+bp)), 1n+k, sat(k, Laws.lcm(acc, 1n+bp)),
        sat_gt(k, Laws.lcm(1n+k, 1n+bp), gt_of_w(Laws.lcm(1n+k, 1n+bp), k, lcm_ge(1n+k, bp))),
        Equal.sym(Nat, sat(k, Laws.lcm(acc, 1n+bp)), 1n+k,
          sat_gt(k, Laws.lcm(acc, 1n+bp), gt_of_w(Laws.lcm(acc, 1n+bp), k,
            le_w_trans(1n+k, acc, Laws.lcm(acc, 1n+bp), le_false_w(acc, k, e), lcm_ge(acc, bp))))))

law lcm_sat:
  for +k: Nat
  for +acc: Nat
  for +bp: Nat
  {L.Limit.lcm(k, sat(k, acc), 1n+bp) == sat(k, Laws.lcm(acc, 1n+bp)) : Nat}

def lcm_sat(k, acc, bp):
  Equal.trans(Nat, L.Limit.lcm(k, sat(k, acc), 1n+bp), sat(k, Laws.lcm(sat(k, acc), 1n+bp)), sat(k, Laws.lcm(acc, 1n+bp)),
    lcm_raw(k, sat(k, acc), bp), lcm_sat.go(k, acc, Nat.is_le(acc, k), {==}, bp))

# Denominators and magnitudes
# ---------------------------

law dens_sat:
  for +k: Nat
  for rs: +List<N.Rat>
  for +acc: Nat
  {L.Limit.dens(k, rs, sat(k, acc)) == sat(k, Laws.den_lcm(rs, acc)) : Nat}

def dens_sat(k, rs, acc):
  match rs:
    case Nil{}:
      {==}
    case Con{N.Rat{+n, +d}, +t}:
      %Equal.sym(Nat, L.Limit.lcm(k, sat(k, acc), 1n+d), sat(k, Laws.lcm(acc, 1n+d)), lcm_sat(k, acc, d))
        : {L.Limit.dens(k, t, _) == sat(k, Laws.den_lcm(t, Laws.lcm(acc, 1n+d))) : Nat}
      dens_sat(k, t, Laws.lcm(acc, 1n+d))

law dens_con:
  for +k: Nat
  for r: N.Rat
  for t: +List<N.Rat>
  for +acc: Nat
  {L.Limit.dens(k, r <> t, acc) == sat(k, Laws.den_lcm(r <> t, acc)) : Nat}

def dens_con(k, r, t, acc):
  match r:
    case N.Rat{n, +d}:
      %Equal.sym(Nat, L.Limit.lcm(k, acc, 1n+d), sat(k, Laws.lcm(acc, 1n+d)), lcm_raw(k, acc, d))
        : {L.Limit.dens(k, t, _) == sat(k, Laws.den_lcm(t, Laws.lcm(acc, 1n+d))) : Nat}
      dens_sat(k, t, Laws.lcm(acc, 1n+d))

law mag_sat:
  for +k: Nat
  for rs: +List<N.Rat>
  for +l: Nat
  {L.Limit.mag(k, rs, l) == sat(k, Laws.mag(rs, l)) : Nat}

def mag_sat(k, rs, l):
  match rs:
    case Nil{}:
      Equal.sym(Nat, sat(k, 0n), 0n, sat_zero(k))
    case Con{N.Rat{+n, +d}, +t}:
      Equal.trans(Nat, Nat.max(L.Limit.mul(k, N.Int.abs(n), Nat.div(l, 1n+d)), L.Limit.mag(k, t, l)),
        Nat.max(sat(k, Nat.mul(N.Int.abs(n), Nat.div(l, 1n+d))), sat(k, Laws.mag(t, l))),
        sat(k, Nat.max(Nat.mul(N.Int.abs(n), Nat.div(l, 1n+d)), Laws.mag(t, l))),
        max_cong(L.Limit.mul(k, N.Int.abs(n), Nat.div(l, 1n+d)), sat(k, Nat.mul(N.Int.abs(n), Nat.div(l, 1n+d))),
          L.Limit.mag(k, t, l), sat(k, Laws.mag(t, l)),
          limit_mul(k, N.Int.abs(n), Nat.div(l, 1n+d)), mag_sat(k, t, l)),
        sat_max(k, Nat.mul(N.Int.abs(n), Nat.div(l, 1n+d)), Laws.mag(t, l)))

# fit's check
# -----------

def spec_x(+n: Nat, +l: Nat, +b: Nat) -> Nat:
  Nat.mul(Nat.mul(Nat.mul(n, n), Nat.mul(b, b)), Nat.max(Nat.mul(2n, b), l))

law fit_inner:
  for +k: Nat
  for +n: Nat
  for +l: Nat
  for +b: Nat
  for h: {Nat.is_le(l, k) == True{} : Bool}
  {L.Limit.mul(k, L.Limit.mul(k, L.Limit.mul(k, n, n), L.Limit.mul(k, sat(k, b), sat(k, b))),
     Nat.max(L.Limit.mul(k, 2n, sat(k, b)), l)) == sat(k, spec_x(n, l, b)) : Nat}

def fit_inner(k, n, l, b, h):
  Equal.trans(Nat,
    L.Limit.mul(k, L.Limit.mul(k, L.Limit.mul(k, n, n), L.Limit.mul(k, sat(k, b), sat(k, b))),
      Nat.max(L.Limit.mul(k, 2n, sat(k, b)), l)),
    L.Limit.mul(k, sat(k, Nat.mul(Nat.mul(n, n), Nat.mul(b, b))), sat(k, Nat.max(Nat.mul(2n, b), l))),
    sat(k, spec_x(n, l, b)),
    lmul_cong(k,
      L.Limit.mul(k, L.Limit.mul(k, n, n), L.Limit.mul(k, sat(k, b), sat(k, b))),
      sat(k, Nat.mul(Nat.mul(n, n), Nat.mul(b, b))),
      Nat.max(L.Limit.mul(k, 2n, sat(k, b)), l), sat(k, Nat.max(Nat.mul(2n, b), l)),
      Equal.trans(Nat, L.Limit.mul(k, L.Limit.mul(k, n, n), L.Limit.mul(k, sat(k, b), sat(k, b))),
        L.Limit.mul(k, sat(k, Nat.mul(n, n)), sat(k, Nat.mul(b, b))),
        sat(k, Nat.mul(Nat.mul(n, n), Nat.mul(b, b))),
        lmul_cong(k, L.Limit.mul(k, n, n), sat(k, Nat.mul(n, n)), L.Limit.mul(k, sat(k, b), sat(k, b)), sat(k, Nat.mul(b, b)),
          limit_mul(k, n, n), lm(k, b, b)),
        lm(k, Nat.mul(n, n), Nat.mul(b, b))),
      Equal.trans(Nat, Nat.max(L.Limit.mul(k, 2n, sat(k, b)), l), Nat.max(sat(k, Nat.mul(2n, b)), sat(k, l)),
        sat(k, Nat.max(Nat.mul(2n, b), l)),
        max_cong(L.Limit.mul(k, 2n, sat(k, b)), sat(k, Nat.mul(2n, b)), l, sat(k, l),
          Equal.trans(Nat, L.Limit.mul(k, 2n, sat(k, b)), sat(k, Nat.mul(2n, sat(k, b))), sat(k, Nat.mul(2n, b)),
            limit_mul(k, 2n, sat(k, b)), sat_mul_r(k, 2n, b)),
          Equal.sym(Nat, sat(k, l), l, sat_le(k, l, h))),
        sat_max(k, Nat.mul(2n, b), l))),
    lm(k, Nat.mul(Nat.mul(n, n), Nat.mul(b, b)), Nat.max(Nat.mul(2n, b), l)))

law fit_go:
  for +k: Nat
  for +n: Nat
  for +l: Nat
  for +b: Nat
  for h: {Nat.is_le(l, k) == True{} : Bool}
  {L.Limit.fit(k, n, l, sat(k, b)) == Laws.fit_fits.go(k, n, l, b) : Bool}

def fit_go(k, n, l, b, h):
  %Equal.sym(Nat,
      L.Limit.mul(k, L.Limit.mul(k, L.Limit.mul(k, n, n), L.Limit.mul(k, sat(k, b), sat(k, b))),
        Nat.max(L.Limit.mul(k, 2n, sat(k, b)), l)),
      sat(k, spec_x(n, l, b)), fit_inner(k, n, l, b, h))
    : {Bool.and(Nat.is_le(l, k), Nat.is_le(_, k)) == Laws.fit_fits.go(k, n, l, b) : Bool}
  %Equal.sym(Bool, Nat.is_le(sat(k, spec_x(n, l, b)), k), Nat.is_le(spec_x(n, l, b), k), ok_sat(k, spec_x(n, l, b)))
    : {Bool.and(Nat.is_le(l, k), _) == Laws.fit_fits.go(k, n, l, b) : Bool}
  {==}

def code_b(+k: Nat, +l: Nat, xs: +List<N.Rat>, ys: +List<N.Rat>) -> Nat:
  Nat.max(L.Limit.mag(k, xs, l), L.Limit.mag(k, ys, l))

def spec_b(+l: Nat, xs: +List<N.Rat>, ys: +List<N.Rat>) -> Nat:
  Nat.max(Laws.mag(xs, l), Laws.mag(ys, l))

law guard_t:
  for +k: Nat
  for +n: Nat
  for +l: Nat
  for +xs: +List<N.Rat>
  for +ys: +List<N.Rat>
  for +h: {Nat.is_le(l, k) == True{} : Bool}
  {L.Limit.fit(k, n, sat(k, l), code_b(k, sat(k, l), xs, ys)) == Laws.fit_fits.go(k, n, l, spec_b(l, xs, ys)) : Bool}

def guard_t(k, n, l, xs, ys, h):
  %Equal.sym(Nat, sat(k, l), l, sat_le(k, l, h))
    : {L.Limit.fit(k, n, _, code_b(k, _, xs, ys)) == Laws.fit_fits.go(k, n, l, spec_b(l, xs, ys)) : Bool}
  Equal.trans(Bool, L.Limit.fit(k, n, l, code_b(k, l, xs, ys)), L.Limit.fit(k, n, l, sat(k, spec_b(l, xs, ys))),
    Laws.fit_fits.go(k, n, l, spec_b(l, xs, ys)),
    Equal.cong(Nat, Bool, z => L.Limit.fit(k, n, l, z), code_b(k, l, xs, ys), sat(k, spec_b(l, xs, ys)),
      Equal.trans(Nat, code_b(k, l, xs, ys), Nat.max(sat(k, Laws.mag(xs, l)), sat(k, Laws.mag(ys, l))), sat(k, spec_b(l, xs, ys)),
        max_cong(L.Limit.mag(k, xs, l), sat(k, Laws.mag(xs, l)), L.Limit.mag(k, ys, l), sat(k, Laws.mag(ys, l)),
          mag_sat(k, xs, l), mag_sat(k, ys, l)),
        sat_max(k, Laws.mag(xs, l), Laws.mag(ys, l)))),
    fit_go(k, n, l, spec_b(l, xs, ys), h))

law guard_f:
  for +k: Nat
  for +n: Nat
  for +l: Nat
  for +xs: +List<N.Rat>
  for +ys: +List<N.Rat>
  for +h: {Nat.is_le(l, k) == False{} : Bool}
  {L.Limit.fit(k, n, sat(k, l), code_b(k, sat(k, l), xs, ys)) == Laws.fit_fits.go(k, n, l, spec_b(l, xs, ys)) : Bool}

def guard_f(k, n, l, xs, ys, h):
  %Equal.sym(Bool, Nat.is_le(sat(k, l), k), Nat.is_le(l, k), ok_sat(k, l))
    : {Bool.and(_, L.Limit.ok(k, L.Limit.mul(k, L.Limit.mul(k, L.Limit.mul(k, n, n),
          L.Limit.mul(k, code_b(k, sat(k, l), xs, ys), code_b(k, sat(k, l), xs, ys))),
          Nat.max(L.Limit.mul(k, 2n, code_b(k, sat(k, l), xs, ys)), sat(k, l)))))
        == Laws.fit_fits.go(k, n, l, spec_b(l, xs, ys)) : Bool}
  %Equal.sym(Bool, Nat.is_le(l, k), False{}, h)
    : {Bool.and(_, L.Limit.ok(k, L.Limit.mul(k, L.Limit.mul(k, L.Limit.mul(k, n, n),
          L.Limit.mul(k, code_b(k, sat(k, l), xs, ys), code_b(k, sat(k, l), xs, ys))),
          Nat.max(L.Limit.mul(k, 2n, code_b(k, sat(k, l), xs, ys)), sat(k, l)))))
        == Bool.and(_, Nat.is_le(spec_x(n, l, spec_b(l, xs, ys)), k)) : Bool}
  {==}

law guard.go:
  for +k: Nat
  for +n: Nat
  for +l: Nat
  for +xs: +List<N.Rat>
  for +ys: +List<N.Rat>
  for b: Bool
  for e: {Nat.is_le(l, k) == b : Bool}
  {L.Limit.fit(k, n, sat(k, l), code_b(k, sat(k, l), xs, ys)) == Laws.fit_fits.go(k, n, l, spec_b(l, xs, ys)) : Bool}

def guard.go(k, n, l, xs, ys, b, e):
  match b:
    case True{}:
      guard_t(k, n, l, xs, ys, e)
    case False{}:
      guard_f(k, n, l, xs, ys, e)

# fit's measured check is fit_fits
law guard:
  for +k: Nat
  for +n: Nat
  for +l: Nat
  for +xs: +List<N.Rat>
  for +ys: +List<N.Rat>
  {L.Limit.fit(k, n, sat(k, l), code_b(k, sat(k, l), xs, ys)) == Laws.fit_fits.go(k, n, l, spec_b(l, xs, ys)) : Bool}

def guard(k, n, l, xs, ys):
  guard.go(k, n, l, xs, ys, Nat.is_le(l, k), {==})

# fit
# ---

law is_eq_refl:
  for +x: Nat
  {Nat.is_eq(x, x) == True{} : Bool}

def is_eq_refl(x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      is_eq_refl(p)

law same_len:
  for x: N.Rat
  for xt: +List<N.Rat>
  for y: N.Rat
  for yt: +List<N.Rat>
  for len: {List.length(&2, N.Rat, xt) == List.length(&2, N.Rat, yt) : Nat}
  {Nat.is_eq(List.length(&2, N.Rat, x <> xt), List.length(&2, N.Rat, y <> yt)) == True{} : Bool}

def same_len(x, xt, y, yt, len):
  %Equal.sym(Nat, List.length(&2, N.Rat, xt), List.length(&2, N.Rat, yt), len)
    : {Nat.is_eq(1n+_, 1n+List.length(&2, N.Rat, yt)) == True{} : Bool}
  is_eq_refl(List.length(&2, N.Rat, yt))

# the exact lcm of every denominator
def lv(xs: +List<N.Rat>, ys: +List<N.Rat>) -> Nat:
  Laws.den_lcm(ys, Laws.den_lcm(xs, 1n))

law fit_l:
  for +k: Nat
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +ys: +List<N.Rat>
  {L.Limit.dens(k, ys, L.Limit.dens(k, x <> xt, 1n)) == sat(k, lv(x <> xt, ys)) : Nat}

def fit_l(k, x, xt, ys):
  Equal.trans(Nat, L.Limit.dens(k, ys, L.Limit.dens(k, x <> xt, 1n)),
    L.Limit.dens(k, ys, sat(k, Laws.den_lcm(x <> xt, 1n))), sat(k, lv(x <> xt, ys)),
    Equal.cong(Nat, Nat, z => L.Limit.dens(k, ys, z), L.Limit.dens(k, x <> xt, 1n), sat(k, Laws.den_lcm(x <> xt, 1n)),
      dens_con(k, x, xt, 1n)),
    dens_sat(k, ys, Laws.den_lcm(x <> xt, 1n)))

# Once the lengths match, fit's check is exactly fit_fits.
law fit_unfold:
  for +k: Nat
  for fi: Bool
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +len: {List.length(&2, N.Rat, xt) == List.length(&2, N.Rat, yt) : Nat}
  {L.LinearRegression.fit.within(k, fi, x <> xt, y <> yt)
    == L.LinearRegression.fit.check(Laws.fit_fits(k, x <> xt, y <> yt), fi, sat(k, lv(x <> xt, y <> yt)), x <> xt, y <> yt)
    : Result<L.FitError, L.LinearRegression>}

def fit_unfold(k, fi, x, xt, y, yt, len):
  %Equal.sym(Bool, Nat.is_eq(List.length(&2, N.Rat, x <> xt), List.length(&2, N.Rat, y <> yt)), True{},
      same_len(x, xt, y, yt, len))
    : {L.LinearRegression.fit.sizes(k, fi, _, x <> xt, y <> yt)
        == L.LinearRegression.fit.check(Laws.fit_fits(k, x <> xt, y <> yt), fi, sat(k, lv(x <> xt, y <> yt)), x <> xt, y <> yt)
        : Result<L.FitError, L.LinearRegression>}
  %Equal.sym(Nat, L.Limit.dens(k, y <> yt, L.Limit.dens(k, x <> xt, 1n)), sat(k, lv(x <> xt, y <> yt)), fit_l(k, x, xt, y <> yt))
    : {L.LinearRegression.fit.check(L.Limit.fit(k, 1n+List.length(&2, N.Rat, yt), _, code_b(k, _, x <> xt, y <> yt)), fi, _, x <> xt, y <> yt)
        == L.LinearRegression.fit.check(Laws.fit_fits(k, x <> xt, y <> yt), fi, sat(k, lv(x <> xt, y <> yt)), x <> xt, y <> yt)
        : Result<L.FitError, L.LinearRegression>}
  %Equal.sym(Bool, L.Limit.fit(k, 1n+List.length(&2, N.Rat, yt), sat(k, lv(x <> xt, y <> yt)),
        code_b(k, sat(k, lv(x <> xt, y <> yt)), x <> xt, y <> yt)),
      Laws.fit_fits.go(k, 1n+List.length(&2, N.Rat, yt), lv(x <> xt, y <> yt), spec_b(lv(x <> xt, y <> yt), x <> xt, y <> yt)),
      guard(k, 1n+List.length(&2, N.Rat, yt), lv(x <> xt, y <> yt), x <> xt, y <> yt))
    : {L.LinearRegression.fit.check(_, fi, sat(k, lv(x <> xt, y <> yt)), x <> xt, y <> yt)
        == L.LinearRegression.fit.check(Laws.fit_fits(k, x <> xt, y <> yt), fi, sat(k, lv(x <> xt, y <> yt)), x <> xt, y <> yt)
        : Result<L.FitError, L.LinearRegression>}
  %len
    : {L.LinearRegression.fit.check(Laws.fit_fits.go(k, 1n+_, lv(x <> xt, y <> yt), spec_b(lv(x <> xt, y <> yt), x <> xt, y <> yt)),
          fi, sat(k, lv(x <> xt, y <> yt)), x <> xt, y <> yt)
        == L.LinearRegression.fit.check(Laws.fit_fits(k, x <> xt, y <> yt), fi, sat(k, lv(x <> xt, y <> yt)), x <> xt, y <> yt)
        : Result<L.FitError, L.LinearRegression>}
  {==}

law fit_too_large:
  for +k: Nat
  for fi: Bool
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for len: {List.length(&2, N.Rat, xt) == List.length(&2, N.Rat, yt) : Nat}
  for big: {Laws.fit_fits(k, x <> xt, y <> yt) == False{} : Bool}
  {L.LinearRegression.fit.within(k, fi, x <> xt, y <> yt) == Fail{L.TooLarge{}} : Result<L.FitError, L.LinearRegression>}

def fit_too_large(k, fi, x, xt, y, yt, len, big):
  %Equal.sym(Result<L.FitError, L.LinearRegression>, L.LinearRegression.fit.within(k, fi, x <> xt, y <> yt),
      L.LinearRegression.fit.check(Laws.fit_fits(k, x <> xt, y <> yt), fi, sat(k, lv(x <> xt, y <> yt)), x <> xt, y <> yt),
      fit_unfold(k, fi, x, xt, y, yt, len))
    : {_ == Fail{L.TooLarge{}} : Result<L.FitError, L.LinearRegression>}
  %Equal.sym(Bool, Laws.fit_fits(k, x <> xt, y <> yt), False{}, big)
    : {L.LinearRegression.fit.check(_, fi, sat(k, lv(x <> xt, y <> yt)), x <> xt, y <> yt) == Fail{L.TooLarge{}}
        : Result<L.FitError, L.LinearRegression>}
  {==}

# predict
# -------

law and_cong:
  for a1: Bool
  for b1: Bool
  for a2: Bool
  for b2: Bool
  for e1: {a1 == b1 : Bool}
  for e2: {a2 == b2 : Bool}
  {Bool.and(a1, a2) == Bool.and(b1, b2) : Bool}

def and_cong(a1, b1, a2, b2, e1, e2):
  %e1 : {Bool.and(a1, a2) == Bool.and(_, b2) : Bool}
  %e2 : {Bool.and(a1, a2) == Bool.and(a1, _) : Bool}
  {==}

def code_w(+k: Nat, +p: Nat, +q: Nat, +r: Nat, +s: Nat, +d: Nat) -> Nat:
  Nat.max(L.Limit.mul(k, p, Nat.div(d, q)), L.Limit.mul(k, r, Nat.div(d, s)))

def spec_w(+p: Nat, +q: Nat, +r: Nat, +s: Nat, +d: Nat) -> Nat:
  Nat.max(Nat.mul(p, Nat.div(d, q)), Nat.mul(r, Nat.div(d, s)))

law code_w_sat:
  for +k: Nat
  for +p: Nat
  for +q: Nat
  for +r: Nat
  for +s: Nat
  for +d: Nat
  {code_w(k, p, q, r, s, d) == sat(k, spec_w(p, q, r, s, d)) : Nat}

def code_w_sat(k, p, q, r, s, d):
  Equal.trans(Nat, code_w(k, p, q, r, s, d),
    Nat.max(sat(k, Nat.mul(p, Nat.div(d, q))), sat(k, Nat.mul(r, Nat.div(d, s)))), sat(k, spec_w(p, q, r, s, d)),
    max_cong(L.Limit.mul(k, p, Nat.div(d, q)), sat(k, Nat.mul(p, Nat.div(d, q))),
      L.Limit.mul(k, r, Nat.div(d, s)), sat(k, Nat.mul(r, Nat.div(d, s))),
      limit_mul(k, p, Nat.div(d, q)), limit_mul(k, r, Nat.div(d, s))),
    sat_max(k, Nat.mul(p, Nat.div(d, q)), Nat.mul(r, Nat.div(d, s))))

law common_t:
  for +k: Nat
  for +p: Nat
  for +q: Nat
  for +r: Nat
  for +s: Nat
  for +d: Nat
  for +h: {Nat.is_le(d, k) == True{} : Bool}
  {L.Limit.ok(k, L.Limit.common.go(k, p, q, r, s, sat(k, d))) == Nat.is_le(Nat.max(d, spec_w(p, q, r, s, d)), k) : Bool}

def common_t(k, p, q, r, s, d, h):
  %Equal.sym(Nat, sat(k, d), d, sat_le(k, d, h))
    : {Nat.is_le(Nat.max(_, code_w(k, p, q, r, s, _)), k) == Nat.is_le(Nat.max(d, spec_w(p, q, r, s, d)), k) : Bool}
  Equal.trans(Bool, Nat.is_le(Nat.max(d, code_w(k, p, q, r, s, d)), k), Nat.is_le(sat(k, Nat.max(d, spec_w(p, q, r, s, d))), k),
    Nat.is_le(Nat.max(d, spec_w(p, q, r, s, d)), k),
    Equal.cong(Nat, Bool, z => Nat.is_le(z, k), Nat.max(d, code_w(k, p, q, r, s, d)), sat(k, Nat.max(d, spec_w(p, q, r, s, d))),
      Equal.trans(Nat, Nat.max(d, code_w(k, p, q, r, s, d)), Nat.max(sat(k, d), sat(k, spec_w(p, q, r, s, d))),
        sat(k, Nat.max(d, spec_w(p, q, r, s, d))),
        max_cong(d, sat(k, d), code_w(k, p, q, r, s, d), sat(k, spec_w(p, q, r, s, d)),
          Equal.sym(Nat, sat(k, d), d, sat_le(k, d, h)), code_w_sat(k, p, q, r, s, d)),
        sat_max(k, d, spec_w(p, q, r, s, d)))),
    ok_sat(k, Nat.max(d, spec_w(p, q, r, s, d))))

law common_f:
  for +k: Nat
  for +p: Nat
  for +q: Nat
  for +r: Nat
  for +s: Nat
  for +d: Nat
  for +h: {Nat.is_le(d, k) == False{} : Bool}
  {L.Limit.ok(k, L.Limit.common.go(k, p, q, r, s, sat(k, d))) == Nat.is_le(Nat.max(d, spec_w(p, q, r, s, d)), k) : Bool}

def common_f(k, p, q, r, s, d, h):
  Equal.trans(Bool, Nat.is_le(Nat.max(sat(k, d), code_w(k, p, q, r, s, sat(k, d))), k), False{},
    Nat.is_le(Nat.max(d, spec_w(p, q, r, s, d)), k),
    Equal.trans(Bool, Nat.is_le(Nat.max(sat(k, d), code_w(k, p, q, r, s, sat(k, d))), k),
      Bool.and(Nat.is_le(sat(k, d), k), Nat.is_le(code_w(k, p, q, r, s, sat(k, d)), k)), False{},
      ok_max(k, sat(k, d), code_w(k, p, q, r, s, sat(k, d))),
      and_f_l(Nat.is_le(sat(k, d), k), Nat.is_le(code_w(k, p, q, r, s, sat(k, d)), k),
        Equal.trans(Bool, Nat.is_le(sat(k, d), k), Nat.is_le(d, k), False{}, ok_sat(k, d), h))),
    Equal.sym(Bool, Nat.is_le(Nat.max(d, spec_w(p, q, r, s, d)), k), False{},
      Equal.trans(Bool, Nat.is_le(Nat.max(d, spec_w(p, q, r, s, d)), k),
        Bool.and(Nat.is_le(d, k), Nat.is_le(spec_w(p, q, r, s, d), k)), False{},
        ok_max(k, d, spec_w(p, q, r, s, d)),
        and_f_l(Nat.is_le(d, k), Nat.is_le(spec_w(p, q, r, s, d), k), h))))

law common_ok.go:
  for +k: Nat
  for +p: Nat
  for +q: Nat
  for +r: Nat
  for +s: Nat
  for +d: Nat
  for b: Bool
  for e: {Nat.is_le(d, k) == b : Bool}
  {L.Limit.ok(k, L.Limit.common.go(k, p, q, r, s, sat(k, d))) == Nat.is_le(Nat.max(d, spec_w(p, q, r, s, d)), k) : Bool}

def common_ok.go(k, p, q, r, s, d, b, e):
  match b:
    case True{}:
      common_t(k, p, q, r, s, d, e)
    case False{}:
      common_f(k, p, q, r, s, d, e)

# predict's model check is the first half of predict_fits
law common_ok:
  for +k: Nat
  for +p: Nat
  for +q: Nat
  for +r: Nat
  for +s: Nat
  for +d: Nat
  {L.Limit.ok(k, L.Limit.common.go(k, p, q, r, s, sat(k, d))) == Nat.is_le(Nat.max(d, spec_w(p, q, r, s, d)), k) : Bool}

def common_ok(k, p, q, r, s, d):
  common_ok.go(k, p, q, r, s, d, Nat.is_le(d, k), {==})

def code_at(+k: Nat, +a: Nat, +b: Nat, +d: Nat, +u: Nat, +v: Nat) -> Nat:
  Nat.max(L.Limit.add(k, L.Limit.mul(k, a, u), L.Limit.mul(k, b, v)), L.Limit.mul(k, d, v))

def spec_at(+a: Nat, +b: Nat, +d: Nat, +u: Nat, +v: Nat) -> Nat:
  Nat.max(Nat.add(Nat.mul(a, u), Nat.mul(b, v)), Nat.mul(d, v))

law at_sat:
  for +k: Nat
  for +a: Nat
  for +b: Nat
  for +d: Nat
  for +u: Nat
  for +v: Nat
  {code_at(k, a, b, d, u, v) == sat(k, spec_at(a, b, d, u, v)) : Nat}

def at_sat(k, a, b, d, u, v):
  %Equal.sym(Nat, L.Limit.mul(k, a, u), sat(k, Nat.mul(a, u)), limit_mul(k, a, u))
    : {Nat.max(L.Limit.add(k, _, L.Limit.mul(k, b, v)), L.Limit.mul(k, d, v)) == sat(k, spec_at(a, b, d, u, v)) : Nat}
  %Equal.sym(Nat, L.Limit.mul(k, b, v), sat(k, Nat.mul(b, v)), limit_mul(k, b, v))
    : {Nat.max(L.Limit.add(k, sat(k, Nat.mul(a, u)), _), L.Limit.mul(k, d, v)) == sat(k, spec_at(a, b, d, u, v)) : Nat}
  %Equal.sym(Nat, L.Limit.mul(k, d, v), sat(k, Nat.mul(d, v)), limit_mul(k, d, v))
    : {Nat.max(L.Limit.add(k, sat(k, Nat.mul(a, u)), sat(k, Nat.mul(b, v))), _) == sat(k, spec_at(a, b, d, u, v)) : Nat}
  %Equal.sym(Nat, L.Limit.add(k, sat(k, Nat.mul(a, u)), sat(k, Nat.mul(b, v))), sat(k, Nat.add(Nat.mul(a, u), Nat.mul(b, v))),
      limit_add(k, Nat.mul(a, u), Nat.mul(b, v)))
    : {Nat.max(_, sat(k, Nat.mul(d, v))) == sat(k, spec_at(a, b, d, u, v)) : Nat}
  sat_max(k, Nat.add(Nat.mul(a, u), Nat.mul(b, v)), Nat.mul(d, v))

# predict's per-point check is predict_fits.xs
law pred_ok:
  for +k: Nat
  for +a: N.Int
  for +b: N.Int
  for +d: Nat
  for xs: +List<N.Rat>
  {L.Limit.ok(k, L.Limit.predict(k, L.Common{a, b, d}, xs)) == Laws.predict_fits.xs(k, N.Int.abs(a), N.Int.abs(b), d, xs) : Bool}

def pred_ok(k, a, b, d, xs):
  match xs:
    case Nil{}:
      PD.le_zero_l(k)
    case Con{N.Rat{+u, +vp}, +t}:
      Equal.trans(Bool,
        Nat.is_le(Nat.max(code_at(k, N.Int.abs(a), N.Int.abs(b), d, N.Int.abs(u), 1n+vp), L.Limit.predict(k, L.Common{a, b, d}, t)), k),
        Bool.and(Nat.is_le(code_at(k, N.Int.abs(a), N.Int.abs(b), d, N.Int.abs(u), 1n+vp), k),
          Nat.is_le(L.Limit.predict(k, L.Common{a, b, d}, t), k)),
        Bool.and(Nat.is_le(spec_at(N.Int.abs(a), N.Int.abs(b), d, N.Int.abs(u), 1n+vp), k),
          Laws.predict_fits.xs(k, N.Int.abs(a), N.Int.abs(b), d, t)),
        ok_max(k, code_at(k, N.Int.abs(a), N.Int.abs(b), d, N.Int.abs(u), 1n+vp), L.Limit.predict(k, L.Common{a, b, d}, t)),
        and_cong(Nat.is_le(code_at(k, N.Int.abs(a), N.Int.abs(b), d, N.Int.abs(u), 1n+vp), k),
          Nat.is_le(spec_at(N.Int.abs(a), N.Int.abs(b), d, N.Int.abs(u), 1n+vp), k),
          Nat.is_le(L.Limit.predict(k, L.Common{a, b, d}, t), k),
          Laws.predict_fits.xs(k, N.Int.abs(a), N.Int.abs(b), d, t),
          Equal.trans(Bool, Nat.is_le(code_at(k, N.Int.abs(a), N.Int.abs(b), d, N.Int.abs(u), 1n+vp), k),
            Nat.is_le(sat(k, spec_at(N.Int.abs(a), N.Int.abs(b), d, N.Int.abs(u), 1n+vp)), k),
            Nat.is_le(spec_at(N.Int.abs(a), N.Int.abs(b), d, N.Int.abs(u), 1n+vp), k),
            Equal.cong(Nat, Bool, z => Nat.is_le(z, k), code_at(k, N.Int.abs(a), N.Int.abs(b), d, N.Int.abs(u), 1n+vp),
              sat(k, spec_at(N.Int.abs(a), N.Int.abs(b), d, N.Int.abs(u), 1n+vp)),
              at_sat(k, N.Int.abs(a), N.Int.abs(b), d, N.Int.abs(u), 1n+vp)),
            ok_sat(k, spec_at(N.Int.abs(a), N.Int.abs(b), d, N.Int.abs(u), 1n+vp))),
          pred_ok(k, a, b, d, t)))

# predict's values
# ----------------

law at_gen:
  for +p: N.Int
  for +q: Nat
  for +r: N.Int
  for +s: Nat
  for +dd: Nat
  for +e1: Nat
  for +e2: Nat
  for +h1: {1n+dd == Nat.mul(1n+q, e1) : Nat}
  for +h2: {1n+dd == Nat.mul(1n+s, e2) : Nat}
  for x: N.Rat
  {L.Common.at(L.Common{N.Int.mul(p, N.Pos{e1}), N.Int.mul(r, N.Pos{e2}), 1n+dd}, x)
    == Laws.at(N.Rat{p, q}, N.Rat{r, s}, x) : N.Rat}

def at_gen(p, q, r, s, dd, e1, e2, h1, h2, x):
  match x:
    case N.Rat{+u, +vp}:
      %Equal.sym(Nat, Nat.sub(N.Nat.mul_pred(dd, vp), 0n), N.Nat.mul_pred(dd, vp), PI.Nat.sub_zero_r(N.Nat.mul_pred(dd, vp)))
        : {N.Rat.reduce(N.Int.add(N.Int.mul(N.Int.mul(p, N.Pos{e1}), u), N.Int.mul(N.Int.mul(r, N.Pos{e2}), N.Pos{1n+vp})), _)
            == Laws.at(N.Rat{p, q}, N.Rat{r, s}, N.Rat{u, vp}) : N.Rat}
      PR.canon_eq(
        N.Rat.reduce(N.Int.add(N.Int.mul(N.Int.mul(p, N.Pos{e1}), u), N.Int.mul(N.Int.mul(r, N.Pos{e2}), N.Pos{1n+vp})), N.Nat.mul_pred(dd, vp)),
        Laws.at(N.Rat{p, q}, N.Rat{r, s}, N.Rat{u, vp}),
        PR.cd_canon(
          N.Rat.reduce(N.Int.add(N.Int.mul(N.Int.mul(p, N.Pos{e1}), u), N.Int.mul(N.Int.mul(r, N.Pos{e2}), N.Pos{1n+vp})), N.Nat.mul_pred(dd, vp)),
          N.Int.add(N.Int.mul(N.Int.mul(p, N.Pos{e1}), u), N.Int.mul(N.Int.mul(r, N.Pos{e2}), N.Pos{1n+vp})), N.Pos{1n+N.Nat.mul_pred(dd, vp)},
          PR.reduce_ok(N.Int.add(N.Int.mul(N.Int.mul(p, N.Pos{e1}), u), N.Int.mul(N.Int.mul(r, N.Pos{e2}), N.Pos{1n+vp})), N.Nat.mul_pred(dd, vp))),
        PR.add_canon(N.Rat.mul(N.Rat{p, q}, N.Rat{u, vp}), N.Rat{r, s}),
        PR.den_same(
          N.Rat.reduce(N.Int.add(N.Int.mul(N.Int.mul(p, N.Pos{e1}), u), N.Int.mul(N.Int.mul(r, N.Pos{e2}), N.Pos{1n+vp})), N.Nat.mul_pred(dd, vp)),
          Laws.at(N.Rat{p, q}, N.Rat{r, s}, N.Rat{u, vp}),
          N.Int.add(N.Int.mul(N.Int.mul(p, N.Pos{e1}), u), N.Int.mul(N.Int.mul(r, N.Pos{e2}), N.Pos{1n+vp})), N.Nat.mul_pred(dd, vp),
          N.Int.add(N.Int.mul(N.Int.mul(p, u), N.Pos{1n+s}), N.Int.mul(r, N.Pos{1n+N.Nat.mul_pred(q, vp)})),
          N.Nat.mul_pred(N.Nat.mul_pred(q, vp), s),
          PR.cd_den(
            N.Rat.reduce(N.Int.add(N.Int.mul(N.Int.mul(p, N.Pos{e1}), u), N.Int.mul(N.Int.mul(r, N.Pos{e2}), N.Pos{1n+vp})), N.Nat.mul_pred(dd, vp)),
            N.Int.add(N.Int.mul(N.Int.mul(p, N.Pos{e1}), u), N.Int.mul(N.Int.mul(r, N.Pos{e2}), N.Pos{1n+vp})), N.Pos{1n+N.Nat.mul_pred(dd, vp)},
            PR.reduce_ok(N.Int.add(N.Int.mul(N.Int.mul(p, N.Pos{e1}), u), N.Int.mul(N.Int.mul(r, N.Pos{e2}), N.Pos{1n+vp})), N.Nat.mul_pred(dd, vp))),
          PR.den_add(N.Rat.mul(N.Rat{p, q}, N.Rat{u, vp}), N.Rat{r, s}, N.Int.mul(p, u), N.Nat.mul_pred(q, vp), r, s,
            PR.den_mul(N.Rat{p, q}, N.Rat{u, vp}, p, q, u, vp, {==}, {==}), {==}),
          Equal.trans(N.Int,
            N.Int.mul(N.Int.add(N.Int.mul(N.Int.mul(p, N.Pos{e1}), u), N.Int.mul(N.Int.mul(r, N.Pos{e2}), N.Pos{1n+vp})),
              N.Pos{1n+N.Nat.mul_pred(N.Nat.mul_pred(q, vp), s)}),
            N.Int.add(
              N.Int.mul(N.Int.mul(N.Int.mul(N.Int.mul(p, u), N.Pos{1n+vp}), N.Pos{1n+s}), N.Int.mul(N.Pos{1n+q}, N.Pos{e1})),
              N.Int.mul(N.Int.mul(N.Int.mul(N.Int.mul(r, N.Pos{1n+vp}), N.Pos{1n+q}), N.Pos{1n+vp}), N.Int.mul(N.Pos{1n+s}, N.Pos{e2}))),
            N.Int.mul(N.Int.add(N.Int.mul(N.Int.mul(p, u), N.Pos{1n+s}), N.Int.mul(r, N.Pos{1n+N.Nat.mul_pred(q, vp)})),
              N.Pos{1n+N.Nat.mul_pred(dd, vp)}),
            PI.IRing.eq(PI.IMul{PI.IAdd{PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{1n}}, PI.IVar{2n}}, PI.IMul{PI.IMul{PI.IVar{3n}, PI.IVar{4n}}, PI.IVar{5n}}}, PI.IMul{PI.IMul{PI.IVar{6n}, PI.IVar{5n}}, PI.IVar{7n}}}, PI.IAdd{PI.IMul{PI.IMul{PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{2n}}, PI.IVar{5n}}, PI.IVar{7n}}, PI.IMul{PI.IVar{6n}, PI.IVar{1n}}}, PI.IMul{PI.IMul{PI.IMul{PI.IMul{PI.IVar{3n}, PI.IVar{5n}}, PI.IVar{6n}}, PI.IVar{5n}}, PI.IMul{PI.IVar{7n}, PI.IVar{4n}}}}, [p, N.Pos{e1}, u, r, N.Pos{e2}, N.Pos{1n+vp}, N.Pos{1n+q}, N.Pos{1n+s}], {==}),
            (%Equal.cong(Nat, N.Int, z => N.Pos{z}, 1n+dd, Nat.mul(1n+q, e1), h1)
               : {N.Int.add(N.Int.mul(N.Int.mul(N.Int.mul(N.Int.mul(p, u), N.Pos{1n+vp}), N.Pos{1n+s}), _),
                    N.Int.mul(N.Int.mul(N.Int.mul(N.Int.mul(r, N.Pos{1n+vp}), N.Pos{1n+q}), N.Pos{1n+vp}), N.Int.mul(N.Pos{1n+s}, N.Pos{e2})))
                  == N.Int.mul(N.Int.add(N.Int.mul(N.Int.mul(p, u), N.Pos{1n+s}), N.Int.mul(r, N.Pos{1n+N.Nat.mul_pred(q, vp)})), N.Pos{1n+N.Nat.mul_pred(dd, vp)}) : N.Int}
             %Equal.cong(Nat, N.Int, z => N.Pos{z}, 1n+dd, Nat.mul(1n+s, e2), h2)
               : {N.Int.add(N.Int.mul(N.Int.mul(N.Int.mul(N.Int.mul(p, u), N.Pos{1n+vp}), N.Pos{1n+s}), N.Pos{1n+dd}),
                    N.Int.mul(N.Int.mul(N.Int.mul(N.Int.mul(r, N.Pos{1n+vp}), N.Pos{1n+q}), N.Pos{1n+vp}), _))
                  == N.Int.mul(N.Int.add(N.Int.mul(N.Int.mul(p, u), N.Pos{1n+s}), N.Int.mul(r, N.Pos{1n+N.Nat.mul_pred(q, vp)})), N.Pos{1n+N.Nat.mul_pred(dd, vp)}) : N.Int}
             PI.IRing.eq(PI.IAdd{PI.IMul{PI.IMul{PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{1n}}, PI.IVar{2n}}, PI.IVar{3n}}, PI.IVar{6n}}, PI.IMul{PI.IMul{PI.IMul{PI.IMul{PI.IVar{4n}, PI.IVar{2n}}, PI.IVar{5n}}, PI.IVar{2n}}, PI.IVar{6n}}}, PI.IMul{PI.IAdd{PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{1n}}, PI.IVar{3n}}, PI.IMul{PI.IVar{4n}, PI.IMul{PI.IVar{5n}, PI.IVar{2n}}}}, PI.IMul{PI.IVar{6n}, PI.IVar{2n}}}, [p, u, N.Pos{1n+vp}, N.Pos{1n+s}, r, N.Pos{1n+q}, N.Pos{1n+dd}], {==})))))

law at_d:
  for +p: N.Int
  for +q: Nat
  for +r: N.Int
  for +s: Nat
  for +d: Nat
  for +e1: Nat
  for +e2: Nat
  for +h1: {d == Nat.mul(1n+q, e1) : Nat}
  for +h2: {d == Nat.mul(1n+s, e2) : Nat}
  for +dd: Nat
  for +hd: {d == 1n+dd : Nat}
  for x: N.Rat
  {L.Common.at(L.Common{N.Int.mul(p, N.Pos{e1}), N.Int.mul(r, N.Pos{e2}), d}, x)
    == Laws.at(N.Rat{p, q}, N.Rat{r, s}, x) : N.Rat}

def at_d(p, q, r, s, d, e1, e2, h1, h2, dd, hd, x):
  match d:
    case 0n:
      Empty.absurd({L.Common.at(L.Common{N.Int.mul(p, N.Pos{e1}), N.Int.mul(r, N.Pos{e2}), 0n}, x)
          == Laws.at(N.Rat{p, q}, N.Rat{r, s}, x) : N.Rat},
        PD.zero_ne_succ(dd, hd))
    case 1n+dp:
      at_gen(p, q, r, s, dp, e1, e2, h1, h2, x)

def cm(+p: N.Int, +q: Nat, +r: N.Int, +s: Nat, +d: Nat) -> L.Common:
  L.Common{N.Int.mul(p, N.Pos{Nat.div(d, 1n+q)}), N.Int.mul(r, N.Pos{Nat.div(d, 1n+s)}), d}

law go_eq:
  for +p: N.Int
  for +q: Nat
  for +r: N.Int
  for +s: Nat
  for +d: Nat
  for +h1: {d == Nat.mul(1n+q, Nat.div(d, 1n+q)) : Nat}
  for +h2: {d == Nat.mul(1n+s, Nat.div(d, 1n+s)) : Nat}
  for +dd: Nat
  for +hd: {d == 1n+dd : Nat}
  for xs: +List<N.Rat>
  {L.LinearRegression.predict.go(cm(p, q, r, s, d), xs) == Laws.predict(N.Rat{p, q}, N.Rat{r, s}, xs) : +List<N.Rat>}

def go_eq(p, q, r, s, d, h1, h2, dd, hd, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %at_d(p, q, r, s, d, Nat.div(d, 1n+q), Nat.div(d, 1n+s), h1, h2, dd, hd, x)
        : {L.Common.at(cm(p, q, r, s, d), x) <> L.LinearRegression.predict.go(cm(p, q, r, s, d), t)
            == _ <> Laws.predict(N.Rat{p, q}, N.Rat{r, s}, t) : +List<N.Rat>}
      %go_eq(p, q, r, s, d, h1, h2, dd, hd, t)
        : {L.Common.at(cm(p, q, r, s, d), x) <> L.LinearRegression.predict.go(cm(p, q, r, s, d), t)
            == L.Common.at(cm(p, q, r, s, d), x) <> _ : +List<N.Rat>}
      {==}

law dv_div.go:
  for +d: Nat
  for +q: Nat
  for +v: Nat
  for +ev: {d == Nat.mul(1n+q, v) : Nat}
  {d == Nat.mul(1n+q, Nat.div(d, 1n+q)) : Nat}

def dv_div.go(d, q, v, ev):
  %Equal.sym(Nat, Nat.div(d, 1n+q), v, PR.div_of(d, q, v, ev)) : {d == Nat.mul(1n+q, _) : Nat}
  ev

law dv_div:
  for +d: Nat
  for +q: Nat
  for dv: PD.Dv(1n+q, d)
  {d == Nat.mul(1n+q, Nat.div(d, 1n+q)) : Nat}

def dv_div(d, q, dv):
  match dv:
    case (+v, ev):
      dv_div.go(d, q, v, ev)

def pd(+q: Nat, +s: Nat) -> Nat:
  Laws.lcm(1n+q, 1n+s)

def g1(+k: Nat, +p: N.Int, +q: Nat, +r: N.Int, +s: Nat) -> Bool:
  Nat.is_le(Nat.max(pd(q, s), spec_w(N.Int.abs(p), 1n+q, N.Int.abs(r), 1n+s, pd(q, s))), k)

def g2(+k: Nat, +p: N.Int, +q: Nat, +r: N.Int, +s: Nat, xs: +List<N.Rat>) -> Bool:
  Laws.predict_fits.xs(k, Nat.mul(N.Int.abs(p), Nat.div(pd(q, s), 1n+q)), Nat.mul(N.Int.abs(r), Nat.div(pd(q, s), 1n+s)), pd(q, s), xs)

law pred_unfold:
  for +k: Nat
  for +fi: Bool
  for +p: N.Int
  for +q: Nat
  for +r: N.Int
  for +s: Nat
  for +xs: +List<N.Rat>
  {L.LinearRegression.predict.within(k, L.LinearRegression{fi, N.Rat{p, q}, N.Rat{r, s}}, xs)
    == L.LinearRegression.predict.model(k, g1(k, p, q, r, s), L.LinearRegression{fi, N.Rat{p, q}, N.Rat{r, s}}, xs)
    : Result<L.FitError, +List<N.Rat>>}

def pred_unfold(k, fi, p, q, r, s, xs):
  %Equal.sym(Nat, L.Limit.lcm(k, 1n+q, 1n+s), sat(k, pd(q, s)), lcm_raw(k, 1n+q, s))
    : {L.LinearRegression.predict.model(k,
          L.Limit.ok(k, L.Limit.common.go(k, N.Int.abs(p), 1n+q, N.Int.abs(r), 1n+s, _)),
          L.LinearRegression{fi, N.Rat{p, q}, N.Rat{r, s}}, xs)
        == L.LinearRegression.predict.model(k, g1(k, p, q, r, s), L.LinearRegression{fi, N.Rat{p, q}, N.Rat{r, s}}, xs)
        : Result<L.FitError, +List<N.Rat>>}
  %Equal.sym(Bool, L.Limit.ok(k, L.Limit.common.go(k, N.Int.abs(p), 1n+q, N.Int.abs(r), 1n+s, sat(k, pd(q, s)))),
      g1(k, p, q, r, s), common_ok(k, N.Int.abs(p), 1n+q, N.Int.abs(r), 1n+s, pd(q, s)))
    : {L.LinearRegression.predict.model(k, _, L.LinearRegression{fi, N.Rat{p, q}, N.Rat{r, s}}, xs)
        == L.LinearRegression.predict.model(k, g1(k, p, q, r, s), L.LinearRegression{fi, N.Rat{p, q}, N.Rat{r, s}}, xs)
        : Result<L.FitError, +List<N.Rat>>}
  {==}

law model_true:
  for +k: Nat
  for +fi: Bool
  for +p: N.Int
  for +q: Nat
  for +r: N.Int
  for +s: Nat
  for +xs: +List<N.Rat>
  {L.LinearRegression.predict.model(k, True{}, L.LinearRegression{fi, N.Rat{p, q}, N.Rat{r, s}}, xs)
    == L.LinearRegression.predict.check(g2(k, p, q, r, s, xs), cm(p, q, r, s, pd(q, s)), xs)
    : Result<L.FitError, +List<N.Rat>>}

def model_true(k, fi, p, q, r, s, xs):
  %Equal.sym(Nat, N.Nat.lcm(1n+q, 1n+s), pd(q, s), lcm_eq(1n+q, s))
    : {L.LinearRegression.predict.check(L.Limit.ok(k, L.Limit.predict(k, cm(p, q, r, s, _), xs)), cm(p, q, r, s, _), xs)
        == L.LinearRegression.predict.check(g2(k, p, q, r, s, xs), cm(p, q, r, s, pd(q, s)), xs)
        : Result<L.FitError, +List<N.Rat>>}
  %Equal.sym(Bool, L.Limit.ok(k, L.Limit.predict(k, cm(p, q, r, s, pd(q, s)), xs)),
      Laws.predict_fits.xs(k, N.Int.abs(N.Int.mul(p, N.Pos{Nat.div(pd(q, s), 1n+q)})), N.Int.abs(N.Int.mul(r, N.Pos{Nat.div(pd(q, s), 1n+s)})), pd(q, s), xs),
      pred_ok(k, N.Int.mul(p, N.Pos{Nat.div(pd(q, s), 1n+q)}), N.Int.mul(r, N.Pos{Nat.div(pd(q, s), 1n+s)}), pd(q, s), xs))
    : {L.LinearRegression.predict.check(_, cm(p, q, r, s, pd(q, s)), xs)
        == L.LinearRegression.predict.check(g2(k, p, q, r, s, xs), cm(p, q, r, s, pd(q, s)), xs)
        : Result<L.FitError, +List<N.Rat>>}
  %Equal.sym(Nat, N.Int.abs(N.Int.mul(p, N.Pos{Nat.div(pd(q, s), 1n+q)})), Nat.mul(N.Int.abs(p), Nat.div(pd(q, s), 1n+q)),
      PR.abs_mul_pos(p, Nat.div(pd(q, s), 1n+q)))
    : {L.LinearRegression.predict.check(
          Laws.predict_fits.xs(k, _, N.Int.abs(N.Int.mul(r, N.Pos{Nat.div(pd(q, s), 1n+s)})), pd(q, s), xs), cm(p, q, r, s, pd(q, s)), xs)
        == L.LinearRegression.predict.check(g2(k, p, q, r, s, xs), cm(p, q, r, s, pd(q, s)), xs)
        : Result<L.FitError, +List<N.Rat>>}
  %Equal.sym(Nat, N.Int.abs(N.Int.mul(r, N.Pos{Nat.div(pd(q, s), 1n+s)})), Nat.mul(N.Int.abs(r), Nat.div(pd(q, s), 1n+s)),
      PR.abs_mul_pos(r, Nat.div(pd(q, s), 1n+s)))
    : {L.LinearRegression.predict.check(
          Laws.predict_fits.xs(k, Nat.mul(N.Int.abs(p), Nat.div(pd(q, s), 1n+q)), _, pd(q, s), xs), cm(p, q, r, s, pd(q, s)), xs)
        == L.LinearRegression.predict.check(g2(k, p, q, r, s, xs), cm(p, q, r, s, pd(q, s)), xs)
        : Result<L.FitError, +List<N.Rat>>}
  {==}

law predict_ok.go:
  for +k: Nat
  for +fi: Bool
  for +p: N.Int
  for +q: Nat
  for +r: N.Int
  for +s: Nat
  for +xs: +List<N.Rat>
  for +small: {Bool.and(g1(k, p, q, r, s), g2(k, p, q, r, s, xs)) == True{} : Bool}
  for dq: PD.Dv(1n+q, pd(q, s))
  for ds: PD.Dv(1n+s, pd(q, s))
  for w: PD.LeW(1n+q, pd(q, s))
  {L.LinearRegression.predict.within(k, L.LinearRegression{fi, N.Rat{p, q}, N.Rat{r, s}}, xs)
    == Done{Laws.predict(N.Rat{p, q}, N.Rat{r, s}, xs)} : Result<L.FitError, +List<N.Rat>>}

def predict_ok.go(k, fi, p, q, r, s, xs, small, dq, ds, w):
  match w:
    case (+c, ec):
      %Equal.sym(Result<L.FitError, +List<N.Rat>>,
          L.LinearRegression.predict.within(k, L.LinearRegression{fi, N.Rat{p, q}, N.Rat{r, s}}, xs),
          L.LinearRegression.predict.model(k, g1(k, p, q, r, s), L.LinearRegression{fi, N.Rat{p, q}, N.Rat{r, s}}, xs),
          pred_unfold(k, fi, p, q, r, s, xs))
        : {_ == Done{Laws.predict(N.Rat{p, q}, N.Rat{r, s}, xs)} : Result<L.FitError, +List<N.Rat>>}
      %Equal.sym(Bool, g1(k, p, q, r, s), True{}, and_t_l(g1(k, p, q, r, s), g2(k, p, q, r, s, xs), small))
        : {L.LinearRegression.predict.model(k, _, L.LinearRegression{fi, N.Rat{p, q}, N.Rat{r, s}}, xs)
            == Done{Laws.predict(N.Rat{p, q}, N.Rat{r, s}, xs)} : Result<L.FitError, +List<N.Rat>>}
      %Equal.sym(Result<L.FitError, +List<N.Rat>>,
          L.LinearRegression.predict.model(k, True{}, L.LinearRegression{fi, N.Rat{p, q}, N.Rat{r, s}}, xs),
          L.LinearRegression.predict.check(g2(k, p, q, r, s, xs), cm(p, q, r, s, pd(q, s)), xs),
          model_true(k, fi, p, q, r, s, xs))
        : {_ == Done{Laws.predict(N.Rat{p, q}, N.Rat{r, s}, xs)} : Result<L.FitError, +List<N.Rat>>}
      %Equal.sym(Bool, g2(k, p, q, r, s, xs), True{}, and_t_r(g1(k, p, q, r, s), g2(k, p, q, r, s, xs), small))
        : {L.LinearRegression.predict.check(_, cm(p, q, r, s, pd(q, s)), xs)
            == Done{Laws.predict(N.Rat{p, q}, N.Rat{r, s}, xs)} : Result<L.FitError, +List<N.Rat>>}
      %go_eq(p, q, r, s, pd(q, s), dv_div(pd(q, s), q, dq), dv_div(pd(q, s), s, ds), Nat.add(q, c), ec, xs)
        : {Done{L.LinearRegression.predict.go(cm(p, q, r, s, pd(q, s)), xs)} == Done{_} : Result<L.FitError, +List<N.Rat>>}
      {==}

law predict_ok.f:
  for +k: Nat
  for +fi: Bool
  for +p: N.Int
  for +q: Nat
  for +r: N.Int
  for +s: Nat
  for +xs: +List<N.Rat>
  for +small: {Bool.and(g1(k, p, q, r, s), g2(k, p, q, r, s, xs)) == True{} : Bool}
  for f: PD.Dv(1n+q, pd(q, s)) & PD.Dv(1n+s, pd(q, s)) & PD.LeW(1n+q, pd(q, s))
  {L.LinearRegression.predict.within(k, L.LinearRegression{fi, N.Rat{p, q}, N.Rat{r, s}}, xs)
    == Done{Laws.predict(N.Rat{p, q}, N.Rat{r, s}, xs)} : Result<L.FitError, +List<N.Rat>>}

def predict_ok.f(k, fi, p, q, r, s, xs, small, f):
  match f:
    case (dq, (ds, w)):
      predict_ok.go(k, fi, p, q, r, s, xs, small, dq, ds, w)

law predict_ok:
  for +k: Nat
  for +fi: Bool
  for a: N.Rat
  for b: N.Rat
  for +xs: +List<N.Rat>
  for small: {Laws.predict_fits(k, a, b, xs) == True{} : Bool}
  {L.LinearRegression.predict.within(k, L.LinearRegression{fi, a, b}, xs)
    == Done{Laws.predict(a, b, xs)} : Result<L.FitError, +List<N.Rat>>}

def predict_ok(k, fi, a, b, xs, small):
  match a b:
    case N.Rat{+p, +q} N.Rat{+r, +s}:
      predict_ok.f(k, fi, p, q, r, s, xs, small, lcm_facts(1n+q, s))

law predict_too_large.go:
  for +k: Nat
  for +fi: Bool
  for +p: N.Int
  for +q: Nat
  for +r: N.Int
  for +s: Nat
  for +xs: +List<N.Rat>
  for g: Bool
  for +eg: {g1(k, p, q, r, s) == g : Bool}
  for big: {Bool.and(g1(k, p, q, r, s), g2(k, p, q, r, s, xs)) == False{} : Bool}
  {L.LinearRegression.predict.within(k, L.LinearRegression{fi, N.Rat{p, q}, N.Rat{r, s}}, xs)
    == Fail{L.TooLarge{}} : Result<L.FitError, +List<N.Rat>>}

def predict_too_large.go(k, fi, p, q, r, s, xs, g, eg, big):
  match g:
    case False{}:
      %Equal.sym(Result<L.FitError, +List<N.Rat>>,
          L.LinearRegression.predict.within(k, L.LinearRegression{fi, N.Rat{p, q}, N.Rat{r, s}}, xs),
          L.LinearRegression.predict.model(k, g1(k, p, q, r, s), L.LinearRegression{fi, N.Rat{p, q}, N.Rat{r, s}}, xs),
          pred_unfold(k, fi, p, q, r, s, xs))
        : {_ == Fail{L.TooLarge{}} : Result<L.FitError, +List<N.Rat>>}
      %Equal.sym(Bool, g1(k, p, q, r, s), False{}, eg)
        : {L.LinearRegression.predict.model(k, _, L.LinearRegression{fi, N.Rat{p, q}, N.Rat{r, s}}, xs)
            == Fail{L.TooLarge{}} : Result<L.FitError, +List<N.Rat>>}
      {==}
    case True{}:
      %Equal.sym(Result<L.FitError, +List<N.Rat>>,
          L.LinearRegression.predict.within(k, L.LinearRegression{fi, N.Rat{p, q}, N.Rat{r, s}}, xs),
          L.LinearRegression.predict.model(k, g1(k, p, q, r, s), L.LinearRegression{fi, N.Rat{p, q}, N.Rat{r, s}}, xs),
          pred_unfold(k, fi, p, q, r, s, xs))
        : {_ == Fail{L.TooLarge{}} : Result<L.FitError, +List<N.Rat>>}
      %Equal.sym(Bool, g1(k, p, q, r, s), True{}, eg)
        : {L.LinearRegression.predict.model(k, _, L.LinearRegression{fi, N.Rat{p, q}, N.Rat{r, s}}, xs)
            == Fail{L.TooLarge{}} : Result<L.FitError, +List<N.Rat>>}
      %Equal.sym(Result<L.FitError, +List<N.Rat>>,
          L.LinearRegression.predict.model(k, True{}, L.LinearRegression{fi, N.Rat{p, q}, N.Rat{r, s}}, xs),
          L.LinearRegression.predict.check(g2(k, p, q, r, s, xs), cm(p, q, r, s, pd(q, s)), xs),
          model_true(k, fi, p, q, r, s, xs))
        : {_ == Fail{L.TooLarge{}} : Result<L.FitError, +List<N.Rat>>}
      %Equal.sym(Bool, g2(k, p, q, r, s, xs), False{},
          Equal.trans(Bool, g2(k, p, q, r, s, xs), Bool.and(g1(k, p, q, r, s), g2(k, p, q, r, s, xs)), False{},
            (%Equal.sym(Bool, g1(k, p, q, r, s), True{}, eg) : {g2(k, p, q, r, s, xs) == Bool.and(_, g2(k, p, q, r, s, xs)) : Bool}
             {==}),
            big))
        : {L.LinearRegression.predict.check(_, cm(p, q, r, s, pd(q, s)), xs) == Fail{L.TooLarge{}} : Result<L.FitError, +List<N.Rat>>}
      {==}

law predict_too_large:
  for +k: Nat
  for +fi: Bool
  for a: N.Rat
  for b: N.Rat
  for +xs: +List<N.Rat>
  for big: {Laws.predict_fits(k, a, b, xs) == False{} : Bool}
  {L.LinearRegression.predict.within(k, L.LinearRegression{fi, a, b}, xs)
    == Fail{L.TooLarge{}} : Result<L.FitError, +List<N.Rat>>}

def predict_too_large(k, fi, a, b, xs, big):
  match a b:
    case N.Rat{+p, +q} N.Rat{+r, +s}:
      predict_too_large.go(k, fi, p, q, r, s, xs, g1(k, p, q, r, s), {==}, big)
