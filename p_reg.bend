import Base
import ./num.bend as N
import ./p_nat.bend as PN
import ./p_ring.bend as R
import ./p_int.bend as PI
import ./p_div.bend as PD
import ./p_rat.bend as PR
import ./p_sum.bend as PS
import ./p_size.bend as PZ
import ./LAWS.bend as Laws
import ./linreg.bend as L

# fit's answers: when it succeeds or reports Degenerate, the normal
# equations, and least squares.

# Int
# ---

law nat_eq_true:
  for +m: Nat
  for +n: Nat
  for +h: {Nat.is_eq(m, n) == True{} : Bool}
  {m == n : Nat}

def nat_eq_true(m, n, h):
  match m n:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, PD.Bool.ft(h))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, PD.Bool.ft(h))
    case 1n+p 1n+q:
      %nat_eq_true(p, q, h) : {1n+p == 1n+_ : Nat}
      {==}

law ieq_true:
  for +a: N.Int
  for +b: N.Int
  for +h: {N.Int.is_eq(a, b) == True{} : Bool}
  {a == b : N.Int}

def ieq_true(a, b, h):
  match a b:
    case N.Pos{m} N.Pos{n}:
      %nat_eq_true(m, n, h) : {N.Pos{m} == N.Pos{_} : N.Int}
      {==}
    case N.Pos{m} N.Neg{n}:
      Empty.absurd({N.Pos{m} == N.Neg{n} : N.Int}, PD.Bool.ft(h))
    case N.Neg{m} N.Pos{n}:
      Empty.absurd({N.Neg{m} == N.Pos{n} : N.Int}, PD.Bool.ft(h))
    case N.Neg{m} N.Neg{n}:
      %Equal.sym(Nat, n, m, nat_eq_true(n, m, h)) : {N.Neg{m} == N.Neg{_} : N.Int}
      {==}

law ieq_refl:
  for +a: N.Int
  {N.Int.is_eq(a, a) == True{} : Bool}

def ieq_refl(a):
  match a:
    case N.Pos{m}:
      PZ.is_eq_refl(m)
    case N.Neg{m}:
      PZ.is_eq_refl(m)

law ieq_of:
  for +a: N.Int
  for +b: N.Int
  for +e: {a == b : N.Int}
  {N.Int.is_eq(a, b) == True{} : Bool}

def ieq_of(a, b, e):
  %e : {N.Int.is_eq(a, _) == True{} : Bool}
  ieq_refl(a)

law isp_add:
  for +a: N.Int
  for +b: N.Int
  for ha: PR.Int.isp(a)
  for hb: PR.Int.isp(b)
  PR.Int.isp(N.Int.add(a, b))

def isp_add(a, b, ha, hb):
  match a b:
    case N.Pos{m} N.Pos{n}:
      Unit{}
    case N.Pos{m} N.Neg{n}:
      match hb:
    case N.Neg{m} _:
      match ha:

law isp_sq:
  for +z: N.Int
  PR.Int.isp(N.Int.mul(z, z))

def isp_sq(z):
  match z:
    case N.Pos{m}:
      Unit{}
    case N.Neg{m}:
      Unit{}

law nat_add_zero_l:
  for +m: Nat
  for +n: Nat
  for +e: {Nat.add(m, n) == 0n : Nat}
  {m == 0n : Nat}

def nat_add_zero_l(m, n, e):
  match m:
    case 0n:
      {==}
    case 1n+p:
      Empty.absurd({1n+p == 0n : Nat}, PD.succ_ne_zero(Nat.add(p, n), e))

law nat_add_zero_r:
  for +m: Nat
  for +n: Nat
  for +e: {Nat.add(m, n) == 0n : Nat}
  {n == 0n : Nat}

def nat_add_zero_r(m, n, e):
  match m:
    case 0n:
      e
    case 1n+p:
      Empty.absurd({n == 0n : Nat}, PD.succ_ne_zero(Nat.add(p, n), e))

# two nonnegative Ints adding to 0 are both 0
law add_zero_l:
  for +a: N.Int
  for +b: N.Int
  for ha: PR.Int.isp(a)
  for hb: PR.Int.isp(b)
  for +e: {N.Int.add(a, b) == N.Pos{0n} : N.Int}
  {a == N.Pos{0n} : N.Int}

def add_zero_l(a, b, ha, hb, e):
  match a b:
    case N.Pos{m} N.Pos{n}:
      %nat_add_zero_l(m, n, PR.pos_inj(Nat.add(m, n), 0n, e)) : {N.Pos{m} == N.Pos{_} : N.Int}
      {==}
    case N.Pos{m} N.Neg{n}:
      match hb:
    case N.Neg{m} _:
      match ha:

law add_zero_r:
  for +a: N.Int
  for +b: N.Int
  for ha: PR.Int.isp(a)
  for hb: PR.Int.isp(b)
  for +e: {N.Int.add(a, b) == N.Pos{0n} : N.Int}
  {b == N.Pos{0n} : N.Int}

def add_zero_r(a, b, ha, hb, e):
  match a b:
    case N.Pos{m} N.Pos{n}:
      %nat_add_zero_r(m, n, PR.pos_inj(Nat.add(m, n), 0n, e)) : {N.Pos{n} == N.Pos{_} : N.Int}
      {==}
    case N.Pos{m} N.Neg{n}:
      match hb:
    case N.Neg{m} _:
      match ha:

law sq_zero:
  for +z: N.Int
  for +e: {N.Int.mul(z, z) == N.Pos{0n} : N.Int}
  {z == N.Pos{0n} : N.Int}

def sq_zero(z, e):
  match z:
    case N.Pos{0n}:
      {==}
    case N.Pos{1n+p}:
      Empty.absurd({N.Pos{1n+p} == N.Pos{0n} : N.Int},
        PD.succ_ne_zero(Nat.add(p, Nat.mul(p, 1n+p)), PR.pos_inj(Nat.mul(1n+p, 1n+p), 0n, e)))
    case N.Neg{m}:
      Empty.absurd({N.Neg{m} == N.Pos{0n} : N.Int},
        PD.succ_ne_zero(Nat.add(m, Nat.mul(m, 1n+m)), PR.pos_inj(Nat.mul(1n+m, 1n+m), 0n, e)))

law sub_eq_zero:
  for +a: N.Int
  for +c: N.Int
  for +e: {N.Int.sub(a, c) == N.Pos{0n} : N.Int}
  {a == c : N.Int}

def sub_eq_zero(a, c, e):
  Equal.trans(N.Int, a, N.Int.add(N.Int.sub(a, c), c), c,
    PI.IRing.eq(PI.IVar{0n}, PI.IAdd{PI.IAdd{PI.IVar{0n}, PI.INeg{PI.IVar{1n}}}, PI.IVar{1n}}, [a, c], {==}),
    (%Equal.sym(N.Int, N.Int.sub(a, c), N.Pos{0n}, e) : {N.Int.add(_, c) == c : N.Int}
     PI.IRing.eq(PI.IAdd{PI.IConst{N.Pos{0n}}, PI.IVar{0n}}, PI.IVar{0n}, [c], {==})))

# Divisibility of every denominator
# ---------------------------------

# every denominator in rs divides l
def dvb(rs: +List<N.Rat>, +l: Nat) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{r, t}:
      Bool.and(Nat.is_eq(Nat.mod(l, Laws.dnat(r)), 0n), dvb(t, l))

law dv_of_mod:
  for +l: Nat
  for +vp: Nat
  for +h: {Nat.is_eq(Nat.mod(l, 1n+vp), 0n) == True{} : Bool}
  {l == Nat.mul(1n+vp, Nat.div(l, 1n+vp)) : Nat}

def dv_of_mod(l, vp, h):
  %PD.div_mod(l, vp) : {_ == Nat.mul(1n+vp, Nat.div(l, 1n+vp)) : Nat}
  %Equal.sym(Nat, Nat.mod(l, 1n+vp), 0n, nat_eq_true(Nat.mod(l, 1n+vp), 0n, h))
    : {Nat.add(Nat.mul(Nat.div(l, 1n+vp), 1n+vp), _) == Nat.mul(1n+vp, Nat.div(l, 1n+vp)) : Nat}
  R.Ring.eq(R.EAdd{R.EMul{R.EVar{0n}, R.EAdd{R.ENum{1n}, R.EVar{1n}}}, R.ENum{0n}}, R.EMul{R.EAdd{R.ENum{1n}, R.EVar{1n}}, R.EVar{0n}}, [Nat.div(l, 1n+vp), vp], {==})

law mod_of_dv:
  for +l: Nat
  for +vp: Nat
  for +w: Nat
  for +e: {l == Nat.mul(1n+vp, w) : Nat}
  {Nat.is_eq(Nat.mod(l, 1n+vp), 0n) == True{} : Bool}

def mod_of_dv(l, vp, w, e):
  %Equal.sym(Nat, Nat.mod(l, 1n+vp), 0n, PD.mod_unique(w, 0n, vp, l,
      Equal.trans(Nat, Nat.add(Nat.mul(w, 1n+vp), 0n), Nat.mul(1n+vp, w), l,
        R.Ring.eq(R.EAdd{R.EMul{R.EVar{0n}, R.EAdd{R.ENum{1n}, R.EVar{1n}}}, R.ENum{0n}}, R.EMul{R.EAdd{R.ENum{1n}, R.EVar{1n}}, R.EVar{0n}}, [w, vp], {==}), Equal.sym(Nat, l, Nat.mul(1n+vp, w), e)),
      PD.le_zero_l(vp)))
    : {Nat.is_eq(_, 0n) == True{} : Bool}
  {==}

law dvb_head:
  for +l: Nat
  for r: N.Rat
  for +t: +List<N.Rat>
  for +h: {dvb(r <> t, l) == True{} : Bool}
  {l == Nat.mul(Laws.dnat(r), Nat.div(l, Laws.dnat(r))) : Nat}

def dvb_head(l, r, t, h):
  match r:
    case N.Rat{n, +vp}:
      dv_of_mod(l, vp, PZ.and_t_l(Nat.is_eq(Nat.mod(l, 1n+vp), 0n), dvb(t, l), h))

law dvb_tail:
  for +l: Nat
  for r: N.Rat
  for +t: +List<N.Rat>
  for +h: {dvb(r <> t, l) == True{} : Bool}
  {dvb(t, l) == True{} : Bool}

def dvb_tail(l, r, t, h):
  PZ.and_t_r(Nat.is_eq(Nat.mod(l, Laws.dnat(r)), 0n), dvb(t, l), h)

law dv_mul:
  for +v: Nat
  for +l: Nat
  for +m: Nat
  for +q: Nat
  for +e: {m == Nat.mul(l, q) : Nat}
  for +el: {l == Nat.mul(v, Nat.div(l, v)) : Nat}
  {m == Nat.mul(v, Nat.mul(Nat.div(l, v), q)) : Nat}

def dv_mul(v, l, m, q, e, el):
  %Equal.sym(Nat, m, Nat.mul(l, q), e) : {_ == Nat.mul(v, Nat.mul(Nat.div(l, v), q)) : Nat}
  %Equal.sym(Nat, l, Nat.mul(v, Nat.div(l, v)), el) : {Nat.mul(_, q) == Nat.mul(v, Nat.mul(Nat.div(l, v), q)) : Nat}
  PN.mul_assoc(v, Nat.div(l, v), q)

# dvb passes to multiples
law dvb_mono:
  for rs: +List<N.Rat>
  for +l: Nat
  for +m: Nat
  for +q: Nat
  for +e: {m == Nat.mul(l, q) : Nat}
  for +h: {dvb(rs, l) == True{} : Bool}
  {dvb(rs, m) == True{} : Bool}

def dvb_mono(rs, l, m, q, e, h):
  match rs:
    case Nil{}:
      {==}
    case Con{N.Rat{+n, +vp}, +t}:
      PZ.and_tt(Nat.is_eq(Nat.mod(m, 1n+vp), 0n), dvb(t, m),
        mod_of_dv(m, vp, Nat.mul(Nat.div(l, 1n+vp), q),
          dv_mul(1n+vp, l, m, q, e, dvb_head(l, N.Rat{n, vp}, t, h))),
        dvb_mono(t, l, m, q, e, dvb_tail(l, N.Rat{n, vp}, t, h)))

law lcm_dvd_l.go:
  for +a: Nat
  for +bp: Nat
  for f: PD.Dv(a, Laws.lcm(a, 1n+bp)) & PD.Dv(1n+bp, Laws.lcm(a, 1n+bp)) & PD.LeW(a, Laws.lcm(a, 1n+bp))
  PD.Dv(a, Laws.lcm(a, 1n+bp))

def lcm_dvd_l.go(a, bp, f):
  match f:
    case (da, rest):
      da

law lcm_dvd_r.go:
  for +a: Nat
  for +bp: Nat
  for f: PD.Dv(a, Laws.lcm(a, 1n+bp)) & PD.Dv(1n+bp, Laws.lcm(a, 1n+bp)) & PD.LeW(a, Laws.lcm(a, 1n+bp))
  PD.Dv(1n+bp, Laws.lcm(a, 1n+bp))

def lcm_dvd_r.go(a, bp, f):
  match f:
    case (da, (db, w)):
      db

law lcm_dvd_l:
  for +a: Nat
  for +bp: Nat
  PD.Dv(a, Laws.lcm(a, 1n+bp))

def lcm_dvd_l(a, bp):
  lcm_dvd_l.go(a, bp, PZ.lcm_facts(a, bp))

law lcm_dvd_r:
  for +a: Nat
  for +bp: Nat
  PD.Dv(1n+bp, Laws.lcm(a, 1n+bp))

def lcm_dvd_r(a, bp):
  lcm_dvd_r.go(a, bp, PZ.lcm_facts(a, bp))

law dv_trans:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for d1: PD.Dv(a, b)
  for d2: PD.Dv(b, c)
  PD.Dv(a, c)

def dv_trans(a, b, c, d1, d2):
  match d1:
    case (+q1, e1):
      match d2:
        case (+q2, e2):
          (Nat.mul(q1, q2),
            (%Equal.sym(Nat, c, Nat.mul(b, q2), e2) : {_ == Nat.mul(a, Nat.mul(q1, q2)) : Nat}
             %Equal.sym(Nat, b, Nat.mul(a, q1), e1) : {Nat.mul(_, q2) == Nat.mul(a, Nat.mul(q1, q2)) : Nat}
             PN.mul_assoc(a, q1, q2)))

# acc divides den_lcm(rs, acc)
law den_lcm_dv:
  for rs: +List<N.Rat>
  for +acc: Nat
  PD.Dv(acc, Laws.den_lcm(rs, acc))

def den_lcm_dv(rs, acc):
  match rs:
    case Nil{}:
      (1n, Equal.sym(Nat, Nat.mul(acc, 1n), acc, PN.mul_one_r(acc)))
    case Con{N.Rat{n, +d}, +t}:
      dv_trans(acc, Laws.lcm(acc, 1n+d), Laws.den_lcm(t, Laws.lcm(acc, 1n+d)),
        lcm_dvd_l(acc, d), den_lcm_dv(t, Laws.lcm(acc, 1n+d)))

law mod_of_dvw:
  for +m: Nat
  for +vp: Nat
  for dv: PD.Dv(1n+vp, m)
  {Nat.is_eq(Nat.mod(m, 1n+vp), 0n) == True{} : Bool}

def mod_of_dvw(m, vp, dv):
  match dv:
    case (+w, e):
      mod_of_dv(m, vp, w, e)

# every denominator in rs divides den_lcm(rs, acc)
law den_lcm_dvb:
  for rs: +List<N.Rat>
  for +acc: Nat
  {dvb(rs, Laws.den_lcm(rs, acc)) == True{} : Bool}

def den_lcm_dvb(rs, acc):
  match rs:
    case Nil{}:
      {==}
    case Con{N.Rat{+n, +d}, +t}:
      PZ.and_tt(Nat.is_eq(Nat.mod(Laws.den_lcm(t, Laws.lcm(acc, 1n+d)), 1n+d), 0n), dvb(t, Laws.den_lcm(t, Laws.lcm(acc, 1n+d))),
        mod_of_dvw(Laws.den_lcm(t, Laws.lcm(acc, 1n+d)), d,
          dv_trans(1n+d, Laws.lcm(acc, 1n+d), Laws.den_lcm(t, Laws.lcm(acc, 1n+d)),
            lcm_dvd_r(acc, d), den_lcm_dv(t, Laws.lcm(acc, 1n+d)))),
        den_lcm_dvb(t, Laws.lcm(acc, 1n+d)))

law dvb_mono_dv:
  for rs: +List<N.Rat>
  for +l: Nat
  for +m: Nat
  for dv: PD.Dv(l, m)
  for +h: {dvb(rs, l) == True{} : Bool}
  {dvb(rs, m) == True{} : Bool}

def dvb_mono_dv(rs, l, m, dv, h):
  match dv:
    case (+q, e):
      dvb_mono(rs, l, m, q, e, h)

law dvb_xs:
  for +xs: +List<N.Rat>
  for +ys: +List<N.Rat>
  {dvb(xs, PZ.lv(xs, ys)) == True{} : Bool}

def dvb_xs(xs, ys):
  dvb_mono_dv(xs, Laws.den_lcm(xs, 1n), PZ.lv(xs, ys), den_lcm_dv(ys, Laws.den_lcm(xs, 1n)), den_lcm_dvb(xs, 1n))

law dvb_ys:
  for +xs: +List<N.Rat>
  for +ys: +List<N.Rat>
  {dvb(ys, PZ.lv(xs, ys)) == True{} : Bool}

def dvb_ys(xs, ys):
  den_lcm_dvb(ys, Laws.den_lcm(xs, 1n))

law den_lcm_ge:
  for rs: +List<N.Rat>
  for +acc: Nat
  PD.LeW(acc, Laws.den_lcm(rs, acc))

def den_lcm_ge(rs, acc):
  match rs:
    case Nil{}:
      PZ.le_w_refl(acc)
    case Con{N.Rat{n, +d}, +t}:
      PZ.le_w_trans(acc, Laws.lcm(acc, 1n+d), Laws.den_lcm(t, Laws.lcm(acc, 1n+d)),
        PZ.lcm_ge(acc, d), den_lcm_ge(t, Laws.lcm(acc, 1n+d)))

# lv >= 1
law lv_pos:
  for +xs: +List<N.Rat>
  for +ys: +List<N.Rat>
  PD.LeW(1n, PZ.lv(xs, ys))

def lv_pos(xs, ys):
  PZ.le_w_trans(1n, Laws.den_lcm(xs, 1n), PZ.lv(xs, ys), den_lcm_ge(xs, 1n), den_lcm_ge(ys, Laws.den_lcm(xs, 1n)))

# Scaling
# -------

law pos_eq:
  for +a: Nat
  for +b: Nat
  for +e: {a == b : Nat}
  {N.Pos{a} == N.Pos{b} : N.Int}

def pos_eq(a, b, e):
  Equal.cong(Nat, N.Int, z => N.Pos{z}, a, b, e)

# equal scaled values mean the same number
law scale_of_same:
  for +l: Nat
  for +a: N.Rat
  for +c: N.Rat
  for +ea: {l == Nat.mul(Laws.dnat(a), Nat.div(l, Laws.dnat(a))) : Nat}
  for +ec: {l == Nat.mul(Laws.dnat(c), Nat.div(l, Laws.dnat(c))) : Nat}
  for +h: {Laws.same(a, c) == True{} : Bool}
  {L.Stats.scale(l, a) == L.Stats.scale(l, c) : N.Int}

def scale_of_same(l, a, c, ea, ec, h):
  match a c:
    case N.Rat{+ua, +va} N.Rat{+uc, +vc}:
      PR.int_cancel(N.Int.mul(ua, N.Pos{Nat.div(l, 1n+va)}), N.Int.mul(uc, N.Pos{Nat.div(l, 1n+vc)}), N.Nat.mul_pred(va, vc),
        Equal.trans(N.Int,
          N.Int.mul(N.Int.mul(ua, N.Pos{Nat.div(l, 1n+va)}), N.Int.mul(N.Pos{1n+va}, N.Pos{1n+vc})),
          N.Int.mul(N.Int.mul(ua, N.Pos{1n+vc}), N.Int.mul(N.Pos{1n+va}, N.Pos{Nat.div(l, 1n+va)})),
          N.Int.mul(N.Int.mul(uc, N.Pos{Nat.div(l, 1n+vc)}), N.Int.mul(N.Pos{1n+va}, N.Pos{1n+vc})),
          PI.IRing.eq(PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{1n}}, PI.IMul{PI.IVar{2n}, PI.IVar{3n}}}, PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{3n}}, PI.IMul{PI.IVar{2n}, PI.IVar{1n}}}, [ua, N.Pos{Nat.div(l, 1n+va)}, N.Pos{1n+va}, N.Pos{1n+vc}], {==}),
          (%Equal.sym(N.Int, N.Int.mul(ua, N.Pos{1n+vc}), N.Int.mul(uc, N.Pos{1n+va}),
               ieq_true(N.Int.mul(ua, N.Pos{1n+vc}), N.Int.mul(uc, N.Pos{1n+va}), h))
             : {N.Int.mul(_, N.Int.mul(N.Pos{1n+va}, N.Pos{Nat.div(l, 1n+va)}))
                 == N.Int.mul(N.Int.mul(uc, N.Pos{Nat.div(l, 1n+vc)}), N.Int.mul(N.Pos{1n+va}, N.Pos{1n+vc})) : N.Int}
           %pos_eq(l, Nat.mul(1n+va, Nat.div(l, 1n+va)), ea)
             : {N.Int.mul(N.Int.mul(uc, N.Pos{1n+va}), _)
                 == N.Int.mul(N.Int.mul(uc, N.Pos{Nat.div(l, 1n+vc)}), N.Int.mul(N.Pos{1n+va}, N.Pos{1n+vc})) : N.Int}
           %Equal.sym(N.Int, N.Pos{l}, N.Pos{Nat.mul(1n+vc, Nat.div(l, 1n+vc))}, pos_eq(l, Nat.mul(1n+vc, Nat.div(l, 1n+vc)), ec))
             : {N.Int.mul(N.Int.mul(uc, N.Pos{1n+va}), _)
                 == N.Int.mul(N.Int.mul(uc, N.Pos{Nat.div(l, 1n+vc)}), N.Int.mul(N.Pos{1n+va}, N.Pos{1n+vc})) : N.Int}
           PI.IRing.eq(PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{1n}}, PI.IMul{PI.IVar{2n}, PI.IVar{3n}}}, PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{3n}}, PI.IMul{PI.IVar{1n}, PI.IVar{2n}}}, [uc, N.Pos{1n+va}, N.Pos{1n+vc}, N.Pos{Nat.div(l, 1n+vc)}], {==}))))

# ...and conversely, once l >= 1
law same_of_scale:
  for +l: Nat
  for +lp: Nat
  for +hl: {l == 1n+lp : Nat}
  for +a: N.Rat
  for +c: N.Rat
  for +ea: {l == Nat.mul(Laws.dnat(a), Nat.div(l, Laws.dnat(a))) : Nat}
  for +ec: {l == Nat.mul(Laws.dnat(c), Nat.div(l, Laws.dnat(c))) : Nat}
  for +h: {L.Stats.scale(l, a) == L.Stats.scale(l, c) : N.Int}
  {Laws.same(a, c) == True{} : Bool}

def same_of_scale(l, lp, hl, a, c, ea, ec, h):
  match a c:
    case N.Rat{+ua, +va} N.Rat{+uc, +vc}:
      ieq_of(N.Int.mul(ua, N.Pos{1n+vc}), N.Int.mul(uc, N.Pos{1n+va}),
        PR.int_cancel(N.Int.mul(ua, N.Pos{1n+vc}), N.Int.mul(uc, N.Pos{1n+va}), lp,
          (%pos_eq(l, 1n+lp, hl)
             : {N.Int.mul(N.Int.mul(ua, N.Pos{1n+vc}), _) == N.Int.mul(N.Int.mul(uc, N.Pos{1n+va}), _) : N.Int}
           %Equal.sym(N.Int, N.Pos{l}, N.Pos{Nat.mul(1n+va, Nat.div(l, 1n+va))}, pos_eq(l, Nat.mul(1n+va, Nat.div(l, 1n+va)), ea))
             : {N.Int.mul(N.Int.mul(ua, N.Pos{1n+vc}), _) == N.Int.mul(N.Int.mul(uc, N.Pos{1n+va}), N.Pos{l}) : N.Int}
           %Equal.sym(N.Int, N.Pos{l}, N.Pos{Nat.mul(1n+vc, Nat.div(l, 1n+vc))}, pos_eq(l, Nat.mul(1n+vc, Nat.div(l, 1n+vc)), ec))
             : {N.Int.mul(N.Int.mul(ua, N.Pos{1n+vc}), N.Int.mul(N.Pos{1n+va}, N.Pos{Nat.div(l, 1n+va)}))
                 == N.Int.mul(N.Int.mul(uc, N.Pos{1n+va}), _) : N.Int}
           Equal.trans(N.Int,
             N.Int.mul(N.Int.mul(ua, N.Pos{1n+vc}), N.Int.mul(N.Pos{1n+va}, N.Pos{Nat.div(l, 1n+va)})),
             N.Int.mul(N.Int.mul(ua, N.Pos{Nat.div(l, 1n+va)}), N.Int.mul(N.Pos{1n+va}, N.Pos{1n+vc})),
             N.Int.mul(N.Int.mul(uc, N.Pos{1n+va}), N.Int.mul(N.Pos{1n+vc}, N.Pos{Nat.div(l, 1n+vc)})),
             PI.IRing.eq(PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{1n}}, PI.IMul{PI.IVar{2n}, PI.IVar{3n}}}, PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{3n}}, PI.IMul{PI.IVar{2n}, PI.IVar{1n}}}, [ua, N.Pos{1n+vc}, N.Pos{1n+va}, N.Pos{Nat.div(l, 1n+va)}], {==}),
             (%Equal.sym(N.Int, N.Int.mul(ua, N.Pos{Nat.div(l, 1n+va)}), N.Int.mul(uc, N.Pos{Nat.div(l, 1n+vc)}), h)
                : {N.Int.mul(_, N.Int.mul(N.Pos{1n+va}, N.Pos{1n+vc}))
                    == N.Int.mul(N.Int.mul(uc, N.Pos{1n+va}), N.Int.mul(N.Pos{1n+vc}, N.Pos{Nat.div(l, 1n+vc)})) : N.Int}
              PI.IRing.eq(PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{1n}}, PI.IMul{PI.IVar{2n}, PI.IVar{3n}}}, PI.IMul{PI.IMul{PI.IVar{0n}, PI.IVar{2n}}, PI.IMul{PI.IVar{3n}, PI.IVar{1n}}}, [uc, N.Pos{Nat.div(l, 1n+vc)}, N.Pos{1n+va}, N.Pos{1n+vc}], {==}))))))

# Sums over the points
# --------------------

def sn(s: L.Stats) -> N.Int:
  match s:
    case L.Stats{n, sx, sy, sxy, sxx}:
      n

def ssx(s: L.Stats) -> N.Int:
  match s:
    case L.Stats{n, sx, sy, sxy, sxx}:
      sx

def ssy(s: L.Stats) -> N.Int:
  match s:
    case L.Stats{n, sx, sy, sxy, sxx}:
      sy

def ssxy(s: L.Stats) -> N.Int:
  match s:
    case L.Stats{n, sx, sy, sxy, sxx}:
      sxy

def ssxx(s: L.Stats) -> N.Int:
  match s:
    case L.Stats{n, sx, sy, sxy, sxx}:
      sxx

# D = n Σx² - (Σx)², solve's denominator
def dexp(+s: L.Stats) -> N.Int:
  N.Int.sub(N.Int.mul(sn(s), ssxx(s)), N.Int.mul(ssx(s), ssx(s)))

# Σ (x - c)², as Σx² - 2cΣx + n c²
def fexp(+s: L.Stats, +c: N.Int) -> N.Int:
  N.Int.add(N.Int.sub(ssxx(s), N.Int.mul(N.Int.mul(N.Pos{2n}, c), ssx(s))), N.Int.mul(N.Int.mul(sn(s), c), c))

def pt(+x: N.Int, +y: N.Int) -> L.Stats:
  L.Stats{N.Pos{1n}, x, y, N.Int.mul(x, y), N.Int.mul(x, x)}

law d_step:
  for +x: N.Int
  for +y: N.Int
  for s: L.Stats
  {dexp(L.Stats.add(pt(x, y), s)) == N.Int.add(dexp(s), fexp(s, x)) : N.Int}

def d_step(x, y, s):
  match s:
    case L.Stats{+n, +sx, sy, sxy, +sxx}:
      PI.IRing.eq(PI.IAdd{PI.IMul{PI.IAdd{PI.IConst{N.Pos{1n}}, PI.IVar{1n}}, PI.IAdd{PI.IMul{PI.IVar{0n}, PI.IVar{0n}}, PI.IVar{3n}}}, PI.INeg{PI.IMul{PI.IAdd{PI.IVar{0n}, PI.IVar{2n}}, PI.IAdd{PI.IVar{0n}, PI.IVar{2n}}}}}, PI.IAdd{PI.IAdd{PI.IMul{PI.IVar{1n}, PI.IVar{3n}}, PI.INeg{PI.IMul{PI.IVar{2n}, PI.IVar{2n}}}}, PI.IAdd{PI.IAdd{PI.IVar{3n}, PI.INeg{PI.IMul{PI.IMul{PI.IConst{N.Pos{2n}}, PI.IVar{0n}}, PI.IVar{2n}}}}, PI.IMul{PI.IMul{PI.IVar{1n}, PI.IVar{0n}}, PI.IVar{0n}}}}, [x, n, sx, sxx], {==})

law f_step:
  for +x: N.Int
  for +y: N.Int
  for s: L.Stats
  for +c: N.Int
  {fexp(L.Stats.add(pt(x, y), s), c) == N.Int.add(N.Int.mul(N.Int.sub(x, c), N.Int.sub(x, c)), fexp(s, c)) : N.Int}

def f_step(x, y, s, c):
  match s:
    case L.Stats{+n, +sx, sy, sxy, +sxx}:
      PI.IRing.eq(PI.IAdd{PI.IAdd{PI.IAdd{PI.IMul{PI.IVar{0n}, PI.IVar{0n}}, PI.IVar{4n}}, PI.INeg{PI.IMul{PI.IMul{PI.IConst{N.Pos{2n}}, PI.IVar{1n}}, PI.IAdd{PI.IVar{0n}, PI.IVar{3n}}}}}, PI.IMul{PI.IMul{PI.IAdd{PI.IConst{N.Pos{1n}}, PI.IVar{2n}}, PI.IVar{1n}}, PI.IVar{1n}}}, PI.IAdd{PI.IMul{PI.IAdd{PI.IVar{0n}, PI.INeg{PI.IVar{1n}}}, PI.IAdd{PI.IVar{0n}, PI.INeg{PI.IVar{1n}}}}, PI.IAdd{PI.IAdd{PI.IVar{4n}, PI.INeg{PI.IMul{PI.IMul{PI.IConst{N.Pos{2n}}, PI.IVar{1n}}, PI.IVar{3n}}}}, PI.IMul{PI.IMul{PI.IVar{2n}, PI.IVar{1n}}, PI.IVar{1n}}}}, [x, c, n, sx, sxx], {==})

law f_zero:
  for +c: N.Int
  {fexp(L.Stats.zero(), c) == N.Pos{0n} : N.Int}

def f_zero(c):
  PI.IRing.eq(PI.IAdd{PI.IAdd{PI.IConst{N.Pos{0n}}, PI.INeg{PI.IMul{PI.IMul{PI.IConst{N.Pos{2n}}, PI.IVar{0n}}, PI.IConst{N.Pos{0n}}}}}, PI.IMul{PI.IMul{PI.IConst{N.Pos{0n}}, PI.IVar{0n}}, PI.IVar{0n}}}, PI.IConst{N.Pos{0n}}, [c], {==})

law sxx_step:
  for +x: N.Int
  for +y: N.Int
  for s: L.Stats
  {ssxx(L.Stats.add(pt(x, y), s)) == N.Int.add(N.Int.mul(x, x), ssxx(s)) : N.Int}

def sxx_step(x, y, s):
  match s:
    case L.Stats{n, sx, sy, sxy, sxx}:
      {==}

law f_nonneg:
  for +l: Nat
  for ps: +List<L.Point>
  for +c: N.Int
  PR.Int.isp(fexp(L.Stats.seq(l, ps), c))

def f_nonneg(l, ps, c):
  match ps:
    case Nil{}:
      %Equal.sym(N.Int, fexp(L.Stats.zero(), c), N.Pos{0n}, f_zero(c)) : PR.Int.isp(_)
      Unit{}
    case Con{L.Pt{+x, +y}, +t}:
      %Equal.sym(N.Int, fexp(L.Stats.add(pt(L.Stats.scale(l, x), L.Stats.scale(l, y)), L.Stats.seq(l, t)), c),
          N.Int.add(N.Int.mul(N.Int.sub(L.Stats.scale(l, x), c), N.Int.sub(L.Stats.scale(l, x), c)), fexp(L.Stats.seq(l, t), c)),
          f_step(L.Stats.scale(l, x), L.Stats.scale(l, y), L.Stats.seq(l, t), c))
        : PR.Int.isp(_)
      isp_add(N.Int.mul(N.Int.sub(L.Stats.scale(l, x), c), N.Int.sub(L.Stats.scale(l, x), c)), fexp(L.Stats.seq(l, t), c),
        isp_sq(N.Int.sub(L.Stats.scale(l, x), c)), f_nonneg(l, t, c))

law d_nonneg:
  for +l: Nat
  for ps: +List<L.Point>
  PR.Int.isp(dexp(L.Stats.seq(l, ps)))

def d_nonneg(l, ps):
  match ps:
    case Nil{}:
      Unit{}
    case Con{L.Pt{+x, +y}, +t}:
      %Equal.sym(N.Int, dexp(L.Stats.add(pt(L.Stats.scale(l, x), L.Stats.scale(l, y)), L.Stats.seq(l, t))),
          N.Int.add(dexp(L.Stats.seq(l, t)), fexp(L.Stats.seq(l, t), L.Stats.scale(l, x))),
          d_step(L.Stats.scale(l, x), L.Stats.scale(l, y), L.Stats.seq(l, t)))
        : PR.Int.isp(_)
      isp_add(dexp(L.Stats.seq(l, t)), fexp(L.Stats.seq(l, t), L.Stats.scale(l, x)),
        d_nonneg(l, t), f_nonneg(l, t, L.Stats.scale(l, x)))

law sxx_nonneg:
  for +l: Nat
  for ps: +List<L.Point>
  PR.Int.isp(ssxx(L.Stats.seq(l, ps)))

def sxx_nonneg(l, ps):
  match ps:
    case Nil{}:
      Unit{}
    case Con{L.Pt{+x, +y}, +t}:
      %Equal.sym(N.Int, ssxx(L.Stats.add(pt(L.Stats.scale(l, x), L.Stats.scale(l, y)), L.Stats.seq(l, t))),
          N.Int.add(N.Int.mul(L.Stats.scale(l, x), L.Stats.scale(l, x)), ssxx(L.Stats.seq(l, t))),
          sxx_step(L.Stats.scale(l, x), L.Stats.scale(l, y), L.Stats.seq(l, t)))
        : PR.Int.isp(_)
      isp_add(N.Int.mul(L.Stats.scale(l, x), L.Stats.scale(l, x)), ssxx(L.Stats.seq(l, t)),
        isp_sq(L.Stats.scale(l, x)), sxx_nonneg(l, t))

def sq(+z: N.Int) -> N.Int:
  N.Int.mul(z, z)

def rest(+l: Nat, xt: +List<N.Rat>, yt: +List<N.Rat>) -> L.Stats:
  L.Stats.seq(l, L.Point.zip(xt, yt))

# all x equal to x0: Σ (x - x0)² = 0 and D = 0
law f_allsame:
  for +l: Nat
  for +x: N.Rat
  for xt: +List<N.Rat>
  for yt: +List<N.Rat>
  for +ex: {l == Nat.mul(Laws.dnat(x), Nat.div(l, Laws.dnat(x))) : Nat}
  for +hd: {dvb(xt, l) == True{} : Bool}
  for +h: {Laws.all_same(x, xt) == True{} : Bool}
  {fexp(rest(l, xt, yt), L.Stats.scale(l, x)) == N.Pos{0n} : N.Int}

def f_allsame(l, x, xt, yt, ex, hd, h):
  match xt yt:
    case Nil{} _:
      f_zero(L.Stats.scale(l, x))
    case Con{xj, xr} Nil{}:
      f_zero(L.Stats.scale(l, x))
    case Con{+xj, +xr} Con{+yj, +yr}:
      %Equal.sym(N.Int, fexp(L.Stats.add(pt(L.Stats.scale(l, xj), L.Stats.scale(l, yj)), rest(l, xr, yr)), L.Stats.scale(l, x)),
          N.Int.add(sq(N.Int.sub(L.Stats.scale(l, xj), L.Stats.scale(l, x))), fexp(rest(l, xr, yr), L.Stats.scale(l, x))),
          f_step(L.Stats.scale(l, xj), L.Stats.scale(l, yj), rest(l, xr, yr), L.Stats.scale(l, x)))
        : {_ == N.Pos{0n} : N.Int}
      %Equal.sym(N.Int, L.Stats.scale(l, xj), L.Stats.scale(l, x),
          scale_of_same(l, xj, x, dvb_head(l, xj, xr, hd), ex,
            PZ.and_t_l(Laws.same(xj, x), Laws.all_same(x, xr), h)))
        : {N.Int.add(sq(N.Int.sub(_, L.Stats.scale(l, x))), fexp(rest(l, xr, yr), L.Stats.scale(l, x))) == N.Pos{0n} : N.Int}
      %Equal.sym(N.Int, fexp(rest(l, xr, yr), L.Stats.scale(l, x)), N.Pos{0n},
          f_allsame(l, x, xr, yr, ex, dvb_tail(l, xj, xr, hd), PZ.and_t_r(Laws.same(xj, x), Laws.all_same(x, xr), h)))
        : {N.Int.add(sq(N.Int.sub(L.Stats.scale(l, x), L.Stats.scale(l, x))), _) == N.Pos{0n} : N.Int}
      PI.IRing.eq(PI.IAdd{PI.IMul{PI.IAdd{PI.IVar{0n}, PI.INeg{PI.IVar{0n}}}, PI.IAdd{PI.IVar{0n}, PI.INeg{PI.IVar{0n}}}}, PI.IConst{N.Pos{0n}}}, PI.IConst{N.Pos{0n}}, [L.Stats.scale(l, x)], {==})

law d_allsame:
  for +l: Nat
  for +x: N.Rat
  for xt: +List<N.Rat>
  for yt: +List<N.Rat>
  for +ex: {l == Nat.mul(Laws.dnat(x), Nat.div(l, Laws.dnat(x))) : Nat}
  for +hd: {dvb(xt, l) == True{} : Bool}
  for +h: {Laws.all_same(x, xt) == True{} : Bool}
  {dexp(rest(l, xt, yt)) == N.Pos{0n} : N.Int}

def d_allsame(l, x, xt, yt, ex, hd, h):
  match xt yt:
    case Nil{} _:
      {==}
    case Con{xj, xr} Nil{}:
      {==}
    case Con{+xj, +xr} Con{+yj, +yr}:
      %Equal.sym(N.Int, dexp(L.Stats.add(pt(L.Stats.scale(l, xj), L.Stats.scale(l, yj)), rest(l, xr, yr))),
          N.Int.add(dexp(rest(l, xr, yr)), fexp(rest(l, xr, yr), L.Stats.scale(l, xj))),
          d_step(L.Stats.scale(l, xj), L.Stats.scale(l, yj), rest(l, xr, yr)))
        : {_ == N.Pos{0n} : N.Int}
      %Equal.sym(N.Int, L.Stats.scale(l, xj), L.Stats.scale(l, x),
          scale_of_same(l, xj, x, dvb_head(l, xj, xr, hd), ex,
            PZ.and_t_l(Laws.same(xj, x), Laws.all_same(x, xr), h)))
        : {N.Int.add(dexp(rest(l, xr, yr)), fexp(rest(l, xr, yr), _)) == N.Pos{0n} : N.Int}
      %Equal.sym(N.Int, dexp(rest(l, xr, yr)), N.Pos{0n},
          d_allsame(l, x, xr, yr, ex, dvb_tail(l, xj, xr, hd), PZ.and_t_r(Laws.same(xj, x), Laws.all_same(x, xr), h)))
        : {N.Int.add(_, fexp(rest(l, xr, yr), L.Stats.scale(l, x))) == N.Pos{0n} : N.Int}
      %Equal.sym(N.Int, fexp(rest(l, xr, yr), L.Stats.scale(l, x)), N.Pos{0n},
          f_allsame(l, x, xr, yr, ex, dvb_tail(l, xj, xr, hd), PZ.and_t_r(Laws.same(xj, x), Laws.all_same(x, xr), h)))
        : {N.Int.add(N.Pos{0n}, _) == N.Pos{0n} : N.Int}
      {==}

law flat_d:
  for +l: Nat
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +ex: {l == Nat.mul(Laws.dnat(x), Nat.div(l, Laws.dnat(x))) : Nat}
  for +hd: {dvb(xt, l) == True{} : Bool}
  for +h: {Laws.all_same(x, xt) == True{} : Bool}
  {dexp(rest(l, x <> xt, y <> yt)) == N.Pos{0n} : N.Int}

def flat_d(l, x, xt, y, yt, ex, hd, h):
  %Equal.sym(N.Int, dexp(L.Stats.add(pt(L.Stats.scale(l, x), L.Stats.scale(l, y)), rest(l, xt, yt))),
      N.Int.add(dexp(rest(l, xt, yt)), fexp(rest(l, xt, yt), L.Stats.scale(l, x))),
      d_step(L.Stats.scale(l, x), L.Stats.scale(l, y), rest(l, xt, yt)))
    : {_ == N.Pos{0n} : N.Int}
  %Equal.sym(N.Int, dexp(rest(l, xt, yt)), N.Pos{0n}, d_allsame(l, x, xt, yt, ex, hd, h))
    : {N.Int.add(_, fexp(rest(l, xt, yt), L.Stats.scale(l, x))) == N.Pos{0n} : N.Int}
  %Equal.sym(N.Int, fexp(rest(l, xt, yt), L.Stats.scale(l, x)), N.Pos{0n}, f_allsame(l, x, xt, yt, ex, hd, h))
    : {N.Int.add(N.Pos{0n}, _) == N.Pos{0n} : N.Int}
  {==}

# Σ (x - x0)² = 0 means every x is x0
law f_zero_same:
  for +l: Nat
  for +lp: Nat
  for +hl: {l == 1n+lp : Nat}
  for +x: N.Rat
  for xt: +List<N.Rat>
  for yt: +List<N.Rat>
  for +len: {List.length(&2, N.Rat, xt) == List.length(&2, N.Rat, yt) : Nat}
  for +ex: {l == Nat.mul(Laws.dnat(x), Nat.div(l, Laws.dnat(x))) : Nat}
  for +hd: {dvb(xt, l) == True{} : Bool}
  for +h: {fexp(rest(l, xt, yt), L.Stats.scale(l, x)) == N.Pos{0n} : N.Int}
  {Laws.all_same(x, xt) == True{} : Bool}

def f_zero_same(l, lp, hl, x, xt, yt, len, ex, hd, h):
  match xt yt:
    case Nil{} _:
      {==}
    case Con{xj, xr} Nil{}:
      Empty.absurd({Laws.all_same(x, xj <> xr) == True{} : Bool}, PD.succ_ne_zero(List.length(&2, N.Rat, xr), len))
    case Con{+xj, +xr} Con{+yj, +yr}:
      PZ.and_tt(Laws.same(xj, x), Laws.all_same(x, xr),
        same_of_scale(l, lp, hl, xj, x, dvb_head(l, xj, xr, hd), ex,
          sub_eq_zero(L.Stats.scale(l, xj), L.Stats.scale(l, x),
            sq_zero(N.Int.sub(L.Stats.scale(l, xj), L.Stats.scale(l, x)),
              add_zero_l(sq(N.Int.sub(L.Stats.scale(l, xj), L.Stats.scale(l, x))), fexp(rest(l, xr, yr), L.Stats.scale(l, x)), isp_sq(N.Int.sub(L.Stats.scale(l, xj), L.Stats.scale(l, x))), f_nonneg(l, L.Point.zip(xr, yr), L.Stats.scale(l, x)),
                Equal.trans(N.Int, N.Int.add(sq(N.Int.sub(L.Stats.scale(l, xj), L.Stats.scale(l, x))), fexp(rest(l, xr, yr), L.Stats.scale(l, x))),
            fexp(L.Stats.add(pt(L.Stats.scale(l, xj), L.Stats.scale(l, yj)), rest(l, xr, yr)), L.Stats.scale(l, x)), N.Pos{0n},
            Equal.sym(N.Int, fexp(L.Stats.add(pt(L.Stats.scale(l, xj), L.Stats.scale(l, yj)), rest(l, xr, yr)), L.Stats.scale(l, x)),
              N.Int.add(sq(N.Int.sub(L.Stats.scale(l, xj), L.Stats.scale(l, x))), fexp(rest(l, xr, yr), L.Stats.scale(l, x))),
              f_step(L.Stats.scale(l, xj), L.Stats.scale(l, yj), rest(l, xr, yr), L.Stats.scale(l, x))),
            h))))),
        f_zero_same(l, lp, hl, x, xr, yr, PD.succ_inj(List.length(&2, N.Rat, xr), List.length(&2, N.Rat, yr), len), ex,
          dvb_tail(l, xj, xr, hd),
          add_zero_r(sq(N.Int.sub(L.Stats.scale(l, xj), L.Stats.scale(l, x))), fexp(rest(l, xr, yr), L.Stats.scale(l, x)), isp_sq(N.Int.sub(L.Stats.scale(l, xj), L.Stats.scale(l, x))), f_nonneg(l, L.Point.zip(xr, yr), L.Stats.scale(l, x)),
            Equal.trans(N.Int, N.Int.add(sq(N.Int.sub(L.Stats.scale(l, xj), L.Stats.scale(l, x))), fexp(rest(l, xr, yr), L.Stats.scale(l, x))),
            fexp(L.Stats.add(pt(L.Stats.scale(l, xj), L.Stats.scale(l, yj)), rest(l, xr, yr)), L.Stats.scale(l, x)), N.Pos{0n},
            Equal.sym(N.Int, fexp(L.Stats.add(pt(L.Stats.scale(l, xj), L.Stats.scale(l, yj)), rest(l, xr, yr)), L.Stats.scale(l, x)),
              N.Int.add(sq(N.Int.sub(L.Stats.scale(l, xj), L.Stats.scale(l, x))), fexp(rest(l, xr, yr), L.Stats.scale(l, x))),
              f_step(L.Stats.scale(l, xj), L.Stats.scale(l, yj), rest(l, xr, yr), L.Stats.scale(l, x))),
            h))))

law spread_d:
  for +l: Nat
  for +lp: Nat
  for +hl: {l == 1n+lp : Nat}
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +len: {List.length(&2, N.Rat, xt) == List.length(&2, N.Rat, yt) : Nat}
  for +ex: {l == Nat.mul(Laws.dnat(x), Nat.div(l, Laws.dnat(x))) : Nat}
  for +hd: {dvb(xt, l) == True{} : Bool}
  for +hz: {dexp(rest(l, x <> xt, y <> yt)) == N.Pos{0n} : N.Int}
  {Laws.all_same(x, xt) == True{} : Bool}

def spread_d(l, lp, hl, x, xt, y, yt, len, ex, hd, hz):
  f_zero_same(l, lp, hl, x, xt, yt, len, ex, hd,
    add_zero_r(dexp(rest(l, xt, yt)), fexp(rest(l, xt, yt), L.Stats.scale(l, x)),
      d_nonneg(l, L.Point.zip(xt, yt)), f_nonneg(l, L.Point.zip(xt, yt), L.Stats.scale(l, x)),
      Equal.trans(N.Int, N.Int.add(dexp(rest(l, xt, yt)), fexp(rest(l, xt, yt), L.Stats.scale(l, x))),
        dexp(L.Stats.add(pt(L.Stats.scale(l, x), L.Stats.scale(l, y)), rest(l, xt, yt))), N.Pos{0n},
        Equal.sym(N.Int, dexp(L.Stats.add(pt(L.Stats.scale(l, x), L.Stats.scale(l, y)), rest(l, xt, yt))),
          N.Int.add(dexp(rest(l, xt, yt)), fexp(rest(l, xt, yt), L.Stats.scale(l, x))),
          d_step(L.Stats.scale(l, x), L.Stats.scale(l, y), rest(l, xt, yt))),
        hz)))

law div_one:
  for +l: Nat
  {l == Nat.mul(1n, Nat.div(l, 1n)) : Nat}

def div_one(l):
  %Equal.sym(Nat, Nat.div(l, 1n), l, PR.div_of(l, 0n, l, Equal.sym(Nat, Nat.add(l, 0n), l, PN.add_zero_r(l))))
    : {l == Nat.mul(1n, _) : Nat}
  Equal.sym(Nat, Nat.add(l, 0n), l, PN.add_zero_r(l))

# every x zero: Σx² = 0
law sxx_allzero:
  for +l: Nat
  for xs: +List<N.Rat>
  for ys: +List<N.Rat>
  for +hd: {dvb(xs, l) == True{} : Bool}
  for +h: {Laws.all_same(N.Rat.zero(), xs) == True{} : Bool}
  {ssxx(rest(l, xs, ys)) == N.Pos{0n} : N.Int}

def sxx_allzero(l, xs, ys, hd, h):
  match xs ys:
    case Nil{} _:
      {==}
    case Con{xj, xr} Nil{}:
      {==}
    case Con{+xj, +xr} Con{+yj, +yr}:
      %Equal.sym(N.Int, ssxx(L.Stats.add(pt(L.Stats.scale(l, xj), L.Stats.scale(l, yj)), rest(l, xr, yr))),
          N.Int.add(sq(L.Stats.scale(l, xj)), ssxx(rest(l, xr, yr))),
          sxx_step(L.Stats.scale(l, xj), L.Stats.scale(l, yj), rest(l, xr, yr)))
        : {_ == N.Pos{0n} : N.Int}
      %Equal.sym(N.Int, L.Stats.scale(l, xj), L.Stats.scale(l, N.Rat.zero()),
          scale_of_same(l, xj, N.Rat.zero(), dvb_head(l, xj, xr, hd), div_one(l),
            PZ.and_t_l(Laws.same(xj, N.Rat.zero()), Laws.all_same(N.Rat.zero(), xr), h)))
        : {N.Int.add(sq(_), ssxx(rest(l, xr, yr))) == N.Pos{0n} : N.Int}
      %Equal.sym(N.Int, ssxx(rest(l, xr, yr)), N.Pos{0n},
          sxx_allzero(l, xr, yr, dvb_tail(l, xj, xr, hd), PZ.and_t_r(Laws.same(xj, N.Rat.zero()), Laws.all_same(N.Rat.zero(), xr), h)))
        : {N.Int.add(sq(L.Stats.scale(l, N.Rat.zero())), _) == N.Pos{0n} : N.Int}
      {==}

# Σx² = 0 means every x is 0
law sxx_zero_same:
  for +l: Nat
  for +lp: Nat
  for +hl: {l == 1n+lp : Nat}
  for xs: +List<N.Rat>
  for ys: +List<N.Rat>
  for +len: {List.length(&2, N.Rat, xs) == List.length(&2, N.Rat, ys) : Nat}
  for +hd: {dvb(xs, l) == True{} : Bool}
  for +h: {ssxx(rest(l, xs, ys)) == N.Pos{0n} : N.Int}
  {Laws.all_same(N.Rat.zero(), xs) == True{} : Bool}

def sxx_zero_same(l, lp, hl, xs, ys, len, hd, h):
  match xs ys:
    case Nil{} _:
      {==}
    case Con{xj, xr} Nil{}:
      Empty.absurd({Laws.all_same(N.Rat.zero(), xj <> xr) == True{} : Bool}, PD.succ_ne_zero(List.length(&2, N.Rat, xr), len))
    case Con{+xj, +xr} Con{+yj, +yr}:
      PZ.and_tt(Laws.same(xj, N.Rat.zero()), Laws.all_same(N.Rat.zero(), xr),
        same_of_scale(l, lp, hl, xj, N.Rat.zero(), dvb_head(l, xj, xr, hd), div_one(l),
          sq_zero(L.Stats.scale(l, xj),
            add_zero_l(sq(L.Stats.scale(l, xj)), ssxx(rest(l, xr, yr)), isp_sq(L.Stats.scale(l, xj)), sxx_nonneg(l, L.Point.zip(xr, yr)),
              Equal.trans(N.Int, N.Int.add(sq(L.Stats.scale(l, xj)), ssxx(rest(l, xr, yr))),
                ssxx(L.Stats.add(pt(L.Stats.scale(l, xj), L.Stats.scale(l, yj)), rest(l, xr, yr))), N.Pos{0n},
                Equal.sym(N.Int, ssxx(L.Stats.add(pt(L.Stats.scale(l, xj), L.Stats.scale(l, yj)), rest(l, xr, yr))),
                  N.Int.add(sq(L.Stats.scale(l, xj)), ssxx(rest(l, xr, yr))),
                  sxx_step(L.Stats.scale(l, xj), L.Stats.scale(l, yj), rest(l, xr, yr))),
                h)))),
        sxx_zero_same(l, lp, hl, xr, yr, PD.succ_inj(List.length(&2, N.Rat, xr), List.length(&2, N.Rat, yr), len),
          dvb_tail(l, xj, xr, hd),
          add_zero_r(sq(L.Stats.scale(l, xj)), ssxx(rest(l, xr, yr)), isp_sq(L.Stats.scale(l, xj)), sxx_nonneg(l, L.Point.zip(xr, yr)),
            Equal.trans(N.Int, N.Int.add(sq(L.Stats.scale(l, xj)), ssxx(rest(l, xr, yr))),
              ssxx(L.Stats.add(pt(L.Stats.scale(l, xj), L.Stats.scale(l, yj)), rest(l, xr, yr))), N.Pos{0n},
              Equal.sym(N.Int, ssxx(L.Stats.add(pt(L.Stats.scale(l, xj), L.Stats.scale(l, yj)), rest(l, xr, yr))),
                N.Int.add(sq(L.Stats.scale(l, xj)), ssxx(rest(l, xr, yr))),
                sxx_step(L.Stats.scale(l, xj), L.Stats.scale(l, yj), rest(l, xr, yr))),
              h))))

# solve
# -----

law ne_of:
  for +z: N.Int
  for +h: {N.Int.is_eq(z, N.Pos{0n}) == False{} : Bool}
  {z != N.Pos{0n} : N.Int}

def ne_of(z, h):
  e => PD.Bool.ft(Equal.trans(Bool, False{}, N.Int.is_eq(z, N.Pos{0n}), True{},
    Equal.sym(Bool, N.Int.is_eq(z, N.Pos{0n}), False{}, h), ieq_of(z, N.Pos{0n}, e)))

law neq_of.go:
  for +z: N.Int
  for b: Bool
  for +e: {N.Int.is_eq(z, N.Pos{0n}) == b : Bool}
  for f: {z == N.Pos{0n} : N.Int} -> Empty
  {N.Int.is_eq(z, N.Pos{0n}) == False{} : Bool}

def neq_of.go(z, b, e, f):
  match b:
    case True{}:
      Empty.absurd({N.Int.is_eq(z, N.Pos{0n}) == False{} : Bool}, f(ieq_true(z, N.Pos{0n}, e)))
    case False{}:
      e

# z == 0 is impossible, as a Bool fact
law neq_of:
  for +z: N.Int
  for f: {z == N.Pos{0n} : N.Int} -> Empty
  {N.Int.is_eq(z, N.Pos{0n}) == False{} : Bool}

def neq_of(z, f):
  neq_of.go(z, N.Int.is_eq(z, N.Pos{0n}), {==}, f)

law solve_flat:
  for +l: Nat
  for s: L.Stats
  for +h: {dexp(s) == N.Pos{0n} : N.Int}
  {L.LinearRegression.solve(l, s) == Fail{L.Degenerate{}} : Result<L.FitError, L.LinearRegression>}

def solve_flat(l, s, h):
  match s:
    case L.Stats{+n, +sx, +sy, +sxy, +sxx}:
      %Equal.sym(N.Int, N.Int.sub(N.Int.mul(n, sxx), N.Int.mul(sx, sx)), N.Pos{0n}, h)
        : {L.LinearRegression.done(True{},
              N.Rat.make(N.Int.sub(N.Int.mul(n, sxy), N.Int.mul(sx, sy)), _),
              N.Rat.make(N.Int.sub(N.Int.mul(sy, sxx), N.Int.mul(sx, sxy)), N.Int.mul(N.Pos{l}, N.Int.sub(N.Int.mul(n, sxx), N.Int.mul(sx, sx)))))
            == Fail{L.Degenerate{}} : Result<L.FitError, L.LinearRegression>}
      {==}

law mul_nz:
  for +l: Nat
  for +lp: Nat
  for +hl: {l == 1n+lp : Nat}
  for +d: N.Int
  for +e: {N.Int.mul(N.Pos{l}, d) == N.Pos{0n} : N.Int}
  {d == N.Pos{0n} : N.Int}

def mul_nz(l, lp, hl, d, e):
  match d:
    case N.Pos{m}:
      %nat_add_zero_l(m, Nat.mul(lp, m),
          PR.pos_inj(Nat.mul(1n+lp, m), 0n, (%hl : {N.Int.mul(N.Pos{_}, N.Pos{m}) == N.Pos{0n} : N.Int}
                                              e)))
        : {N.Pos{m} == N.Pos{_} : N.Int}
      {==}
    case N.Neg{m}:
      Empty.absurd({N.Neg{m} == N.Pos{0n} : N.Int},
        PR.pos_ne_neg(0n, Nat.add(m, Nat.mul(lp, 1n+m)),
          Equal.sym(N.Int, N.Neg{Nat.add(m, Nat.mul(lp, 1n+m))}, N.Pos{0n},
            (%hl : {N.Int.mul(N.Pos{_}, N.Neg{m}) == N.Pos{0n} : N.Int}
             e))))

law solve_ok.go:
  for +l: Nat
  for +a: N.Int
  for +ad: N.Int
  for +b: N.Int
  for +bd: N.Int
  for p1: &r: N.Rat -> {N.Rat.make(a, ad) == Some{r} : Maybe<N.Rat>} & Laws.Canon(r) & Laws.Denotes(r, a, ad)
  for p2: &r: N.Rat -> {N.Rat.make(b, bd) == Some{r} : Maybe<N.Rat>} & Laws.Canon(r) & Laws.Denotes(r, b, bd)
  exs m: L.LinearRegression
  {L.LinearRegression.done(True{}, N.Rat.make(a, ad), N.Rat.make(b, bd)) == Done{m} : Result<L.FitError, L.LinearRegression>}

def solve_ok.go(l, a, ad, b, bd, p1, p2):
  match p1:
    case (+r1, (e1, c1)):
      match p2:
        case (+r2, (e2, c2)):
          (L.LinearRegression{True{}, r1, r2},
            (%Equal.sym(Maybe<N.Rat>, N.Rat.make(a, ad), Some{r1}, e1)
               : {L.LinearRegression.done(True{}, _, N.Rat.make(b, bd)) == Done{L.LinearRegression{True{}, r1, r2}}
                   : Result<L.FitError, L.LinearRegression>}
             %Equal.sym(Maybe<N.Rat>, N.Rat.make(b, bd), Some{r2}, e2)
               : {L.LinearRegression.done(True{}, Some{r1}, _) == Done{L.LinearRegression{True{}, r1, r2}}
                   : Result<L.FitError, L.LinearRegression>}
             {==}))

law solve_ok:
  for +l: Nat
  for +lp: Nat
  for +hl: {l == 1n+lp : Nat}
  for s: L.Stats
  for +nz: {N.Int.is_eq(dexp(s), N.Pos{0n}) == False{} : Bool}
  exs m: L.LinearRegression
  {L.LinearRegression.solve(l, s) == Done{m} : Result<L.FitError, L.LinearRegression>}

def solve_ok(l, lp, hl, s, nz):
  match s:
    case L.Stats{+n, +sx, +sy, +sxy, +sxx}:
      solve_ok.go(l,
        N.Int.sub(N.Int.mul(n, sxy), N.Int.mul(sx, sy)), N.Int.sub(N.Int.mul(n, sxx), N.Int.mul(sx, sx)),
        N.Int.sub(N.Int.mul(sy, sxx), N.Int.mul(sx, sxy)), N.Int.mul(N.Pos{l}, N.Int.sub(N.Int.mul(n, sxx), N.Int.mul(sx, sx))),
        PR.make_ok(N.Int.sub(N.Int.mul(n, sxy), N.Int.mul(sx, sy)), N.Int.sub(N.Int.mul(n, sxx), N.Int.mul(sx, sx)),
          ne_of(N.Int.sub(N.Int.mul(n, sxx), N.Int.mul(sx, sx)), nz)),
        PR.make_ok(N.Int.sub(N.Int.mul(sy, sxx), N.Int.mul(sx, sxy)), N.Int.mul(N.Pos{l}, N.Int.sub(N.Int.mul(n, sxx), N.Int.mul(sx, sx))),
          e => ne_of(N.Int.sub(N.Int.mul(n, sxx), N.Int.mul(sx, sx)), nz)(mul_nz(l, lp, hl, N.Int.sub(N.Int.mul(n, sxx), N.Int.mul(sx, sx)), e))))

law solve_origin_flat:
  for s: L.Stats
  for +h: {ssxx(s) == N.Pos{0n} : N.Int}
  {L.LinearRegression.solve_origin(s) == Fail{L.Degenerate{}} : Result<L.FitError, L.LinearRegression>}

def solve_origin_flat(s, h):
  match s:
    case L.Stats{n, sx, sy, +sxy, +sxx}:
      %Equal.sym(N.Int, sxx, N.Pos{0n}, h)
        : {L.LinearRegression.done(False{}, N.Rat.make(sxy, _), Some{N.Rat.zero()}) == Fail{L.Degenerate{}}
            : Result<L.FitError, L.LinearRegression>}
      {==}

law solve_origin_ok.go:
  for +a: N.Int
  for +ad: N.Int
  for p1: &r: N.Rat -> {N.Rat.make(a, ad) == Some{r} : Maybe<N.Rat>} & Laws.Canon(r) & Laws.Denotes(r, a, ad)
  exs m: L.LinearRegression
  {L.LinearRegression.done(False{}, N.Rat.make(a, ad), Some{N.Rat.zero()}) == Done{m} : Result<L.FitError, L.LinearRegression>}

def solve_origin_ok.go(a, ad, p1):
  match p1:
    case (+r1, (e1, c1)):
      (L.LinearRegression{False{}, r1, N.Rat.zero()},
        (%Equal.sym(Maybe<N.Rat>, N.Rat.make(a, ad), Some{r1}, e1)
           : {L.LinearRegression.done(False{}, _, Some{N.Rat.zero()}) == Done{L.LinearRegression{False{}, r1, N.Rat.zero()}}
               : Result<L.FitError, L.LinearRegression>}
         {==}))

law solve_origin_ok:
  for s: L.Stats
  for +nz: {N.Int.is_eq(ssxx(s), N.Pos{0n}) == False{} : Bool}
  exs m: L.LinearRegression
  {L.LinearRegression.solve_origin(s) == Done{m} : Result<L.FitError, L.LinearRegression>}

def solve_origin_ok(s, nz):
  match s:
    case L.Stats{n, sx, sy, +sxy, +sxx}:
      solve_origin_ok.go(sxy, sxx, PR.make_ok(sxy, sxx, ne_of(sxx, nz)))

# fit
# ---

# Within the size limit, fit solves the sequential sums at l = lv exactly.
law fit_small:
  for +k: Nat
  for +fi: Bool
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +len: {List.length(&2, N.Rat, xt) == List.length(&2, N.Rat, yt) : Nat}
  for +small: {Laws.fit_fits(k, x <> xt, y <> yt) == True{} : Bool}
  {L.LinearRegression.fit.within(k, fi, x <> xt, y <> yt)
    == L.LinearRegression.fit.stats(fi, PZ.lv(x <> xt, y <> yt), rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt))
    : Result<L.FitError, L.LinearRegression>}

def fit_small(k, fi, x, xt, y, yt, len, small):
  %Equal.sym(Result<L.FitError, L.LinearRegression>, L.LinearRegression.fit.within(k, fi, x <> xt, y <> yt),
      L.LinearRegression.fit.check(Laws.fit_fits(k, x <> xt, y <> yt), fi, PZ.sat(k, PZ.lv(x <> xt, y <> yt)), x <> xt, y <> yt),
      PZ.fit_unfold(k, fi, x, xt, y, yt, len))
    : {_ == L.LinearRegression.fit.stats(fi, PZ.lv(x <> xt, y <> yt), rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt))
        : Result<L.FitError, L.LinearRegression>}
  %Equal.sym(Bool, Laws.fit_fits(k, x <> xt, y <> yt), True{}, small)
    : {L.LinearRegression.fit.check(_, fi, PZ.sat(k, PZ.lv(x <> xt, y <> yt)), x <> xt, y <> yt)
        == L.LinearRegression.fit.stats(fi, PZ.lv(x <> xt, y <> yt), rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt))
        : Result<L.FitError, L.LinearRegression>}
  %Equal.sym(Nat, PZ.sat(k, PZ.lv(x <> xt, y <> yt)), PZ.lv(x <> xt, y <> yt),
      PZ.sat_le(k, PZ.lv(x <> xt, y <> yt),
        PZ.and_t_l(Nat.is_le(PZ.lv(x <> xt, y <> yt), k),
          Nat.is_le(PZ.spec_x(List.length(&2, N.Rat, x <> xt), PZ.lv(x <> xt, y <> yt), PZ.spec_b(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), k),
          small)))
    : {L.LinearRegression.fit.stats(fi, _, L.Stats.par(_, L.Point.zip(x <> xt, y <> yt)))
        == L.LinearRegression.fit.stats(fi, PZ.lv(x <> xt, y <> yt), rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt))
        : Result<L.FitError, L.LinearRegression>}
  %Equal.sym(L.Stats, L.Stats.par(PZ.lv(x <> xt, y <> yt), L.Point.zip(x <> xt, y <> yt)), rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt),
      PS.par_seq(PZ.lv(x <> xt, y <> yt), L.Point.zip(x <> xt, y <> yt)))
    : {L.LinearRegression.fit.stats(fi, PZ.lv(x <> xt, y <> yt), _)
        == L.LinearRegression.fit.stats(fi, PZ.lv(x <> xt, y <> yt), rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt))
        : Result<L.FitError, L.LinearRegression>}
  {==}

law fit_flat:
  for +k: Nat
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +len: {List.length(&2, N.Rat, xt) == List.length(&2, N.Rat, yt) : Nat}
  for +small: {Laws.fit_fits(k, x <> xt, y <> yt) == True{} : Bool}
  for +flat: {Laws.all_same(x, xt) == True{} : Bool}
  {L.LinearRegression.fit.within(k, True{}, x <> xt, y <> yt) == Fail{L.Degenerate{}} : Result<L.FitError, L.LinearRegression>}

def fit_flat(k, x, xt, y, yt, len, small, flat):
  Equal.trans(Result<L.FitError, L.LinearRegression>, L.LinearRegression.fit.within(k, True{}, x <> xt, y <> yt),
    L.LinearRegression.fit.stats(True{}, PZ.lv(x <> xt, y <> yt), rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)),
    Fail{L.Degenerate{}},
    fit_small(k, True{}, x, xt, y, yt, len, small),
    solve_flat(PZ.lv(x <> xt, y <> yt), rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt),
      flat_d(PZ.lv(x <> xt, y <> yt), x, xt, y, yt,
        dvb_head(PZ.lv(x <> xt, y <> yt), x, xt, dvb_xs(x <> xt, y <> yt)),
        dvb_tail(PZ.lv(x <> xt, y <> yt), x, xt, dvb_xs(x <> xt, y <> yt)), flat)))

law fit_origin_flat:
  for +k: Nat
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +len: {List.length(&2, N.Rat, xt) == List.length(&2, N.Rat, yt) : Nat}
  for +small: {Laws.fit_fits(k, x <> xt, y <> yt) == True{} : Bool}
  for +zero: {Laws.all_same(N.Rat.zero(), x <> xt) == True{} : Bool}
  {L.LinearRegression.fit.within(k, False{}, x <> xt, y <> yt) == Fail{L.Degenerate{}} : Result<L.FitError, L.LinearRegression>}

def fit_origin_flat(k, x, xt, y, yt, len, small, zero):
  Equal.trans(Result<L.FitError, L.LinearRegression>, L.LinearRegression.fit.within(k, False{}, x <> xt, y <> yt),
    L.LinearRegression.fit.stats(False{}, PZ.lv(x <> xt, y <> yt), rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)),
    Fail{L.Degenerate{}},
    fit_small(k, False{}, x, xt, y, yt, len, small),
    solve_origin_flat(rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt),
      sxx_allzero(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt, dvb_xs(x <> xt, y <> yt), zero)))

law fit_done:
  for +k: Nat
  for +fi: Bool
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +len: {List.length(&2, N.Rat, xt) == List.length(&2, N.Rat, yt) : Nat}
  for +small: {Laws.fit_fits(k, x <> xt, y <> yt) == True{} : Bool}
  for p: &m: L.LinearRegression ->
    {L.LinearRegression.fit.stats(fi, PZ.lv(x <> xt, y <> yt), rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)) == Done{m}
      : Result<L.FitError, L.LinearRegression>}
  exs m: L.LinearRegression
  {L.LinearRegression.fit.within(k, fi, x <> xt, y <> yt) == Done{m} : Result<L.FitError, L.LinearRegression>}

def fit_done(k, fi, x, xt, y, yt, len, small, p):
  match p:
    case (+m, e):
      (m, Equal.trans(Result<L.FitError, L.LinearRegression>, L.LinearRegression.fit.within(k, fi, x <> xt, y <> yt),
        L.LinearRegression.fit.stats(fi, PZ.lv(x <> xt, y <> yt), rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)), Done{m},
        fit_small(k, fi, x, xt, y, yt, len, small), e))

law fit_ok.h:
  for +k: Nat
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +len: {List.length(&2, N.Rat, xt) == List.length(&2, N.Rat, yt) : Nat}
  for +small: {Laws.fit_fits(k, x <> xt, y <> yt) == True{} : Bool}
  for +spread: {Laws.all_same(x, xt) == False{} : Bool}
  for +lp: Nat
  for +hl: {PZ.lv(x <> xt, y <> yt) == 1n+lp : Nat}
  exs m: L.LinearRegression
  {L.LinearRegression.fit.within(k, True{}, x <> xt, y <> yt) == Done{m} : Result<L.FitError, L.LinearRegression>}

def fit_ok.h(k, x, xt, y, yt, len, small, spread, lp, hl):
  fit_done(k, True{}, x, xt, y, yt, len, small,
    solve_ok(PZ.lv(x <> xt, y <> yt), lp, hl, rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt),
      neq_of(dexp(rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)),
        hz => PD.Bool.ft(Equal.trans(Bool, False{}, Laws.all_same(x, xt), True{},
          Equal.sym(Bool, Laws.all_same(x, xt), False{}, spread),
          spread_d(PZ.lv(x <> xt, y <> yt), lp, hl, x, xt, y, yt, len,
            dvb_head(PZ.lv(x <> xt, y <> yt), x, xt, dvb_xs(x <> xt, y <> yt)),
            dvb_tail(PZ.lv(x <> xt, y <> yt), x, xt, dvb_xs(x <> xt, y <> yt)), hz))))))

law fit_ok.go:
  for +k: Nat
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +len: {List.length(&2, N.Rat, xt) == List.length(&2, N.Rat, yt) : Nat}
  for +small: {Laws.fit_fits(k, x <> xt, y <> yt) == True{} : Bool}
  for +spread: {Laws.all_same(x, xt) == False{} : Bool}
  for w: PD.LeW(1n, PZ.lv(x <> xt, y <> yt))
  exs m: L.LinearRegression
  {L.LinearRegression.fit.within(k, True{}, x <> xt, y <> yt) == Done{m} : Result<L.FitError, L.LinearRegression>}

def fit_ok.go(k, x, xt, y, yt, len, small, spread, w):
  match w:
    case (+lp, hl):
      fit_ok.h(k, x, xt, y, yt, len, small, spread, lp, hl)

law fit_ok:
  for +k: Nat
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +len: {List.length(&2, N.Rat, xt) == List.length(&2, N.Rat, yt) : Nat}
  for +small: {Laws.fit_fits(k, x <> xt, y <> yt) == True{} : Bool}
  for +spread: {Laws.all_same(x, xt) == False{} : Bool}
  exs m: L.LinearRegression
  {L.LinearRegression.fit.within(k, True{}, x <> xt, y <> yt) == Done{m} : Result<L.FitError, L.LinearRegression>}

def fit_ok(k, x, xt, y, yt, len, small, spread):
  fit_ok.go(k, x, xt, y, yt, len, small, spread, lv_pos(x <> xt, y <> yt))

law fit_origin_ok.h:
  for +k: Nat
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +len: {List.length(&2, N.Rat, xt) == List.length(&2, N.Rat, yt) : Nat}
  for +small: {Laws.fit_fits(k, x <> xt, y <> yt) == True{} : Bool}
  for +nonzero: {Laws.all_same(N.Rat.zero(), x <> xt) == False{} : Bool}
  for +lp: Nat
  for +hl: {PZ.lv(x <> xt, y <> yt) == 1n+lp : Nat}
  exs m: L.LinearRegression
  {L.LinearRegression.fit.within(k, False{}, x <> xt, y <> yt) == Done{m} : Result<L.FitError, L.LinearRegression>}

def fit_origin_ok.h(k, x, xt, y, yt, len, small, nonzero, lp, hl):
  fit_done(k, False{}, x, xt, y, yt, len, small,
    solve_origin_ok(rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt),
      neq_of(ssxx(rest(PZ.lv(x <> xt, y <> yt), x <> xt, y <> yt)),
        hz => PD.Bool.ft(Equal.trans(Bool, False{}, Laws.all_same(N.Rat.zero(), x <> xt), True{},
          Equal.sym(Bool, Laws.all_same(N.Rat.zero(), x <> xt), False{}, nonzero),
          sxx_zero_same(PZ.lv(x <> xt, y <> yt), lp, hl, x <> xt, y <> yt,
            Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, N.Rat, xt), List.length(&2, N.Rat, yt), len),
            dvb_xs(x <> xt, y <> yt), hz))))))

law fit_origin_ok.go:
  for +k: Nat
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +len: {List.length(&2, N.Rat, xt) == List.length(&2, N.Rat, yt) : Nat}
  for +small: {Laws.fit_fits(k, x <> xt, y <> yt) == True{} : Bool}
  for +nonzero: {Laws.all_same(N.Rat.zero(), x <> xt) == False{} : Bool}
  for w: PD.LeW(1n, PZ.lv(x <> xt, y <> yt))
  exs m: L.LinearRegression
  {L.LinearRegression.fit.within(k, False{}, x <> xt, y <> yt) == Done{m} : Result<L.FitError, L.LinearRegression>}

def fit_origin_ok.go(k, x, xt, y, yt, len, small, nonzero, w):
  match w:
    case (+lp, hl):
      fit_origin_ok.h(k, x, xt, y, yt, len, small, nonzero, lp, hl)

law fit_origin_ok:
  for +k: Nat
  for +x: N.Rat
  for +xt: +List<N.Rat>
  for +y: N.Rat
  for +yt: +List<N.Rat>
  for +len: {List.length(&2, N.Rat, xt) == List.length(&2, N.Rat, yt) : Nat}
  for +small: {Laws.fit_fits(k, x <> xt, y <> yt) == True{} : Bool}
  for +nonzero: {Laws.all_same(N.Rat.zero(), x <> xt) == False{} : Bool}
  exs m: L.LinearRegression
  {L.LinearRegression.fit.within(k, False{}, x <> xt, y <> yt) == Done{m} : Result<L.FitError, L.LinearRegression>}

def fit_origin_ok(k, x, xt, y, yt, len, small, nonzero):
  fit_origin_ok.go(k, x, xt, y, yt, len, small, nonzero, lv_pos(x <> xt, y <> yt))
