import Base
import ./num.bend as N
import ./LAWS.bend as Laws
import ./p_int.bend as PI
import ./p_div.bend as PD
import ./p_rat.bend as PR
import ./p_sum.bend as PS
import ./p_size.bend as PZ
import ./p_reg.bend as PRG
import ./p_ls.bend as PLS
import ./linreg.bend as L

# Proofs of LAWS.bend. Each law is proven by the def of the same name; the
# work happens in the p_*.bend files.

# Int
# ---

def Laws.Int.sub_nat_zero(a):
  PI.sub_nat_zero(a)

def Laws.Int.sub_nat_neg(b):
  PI.sub_nat_neg(b)

def Laws.Int.sub_nat_succ(a, b):
  PI.sub_nat_succ(a, b)

def Laws.Int.neg_def(a, b):
  PI.neg_def(a, b)

def Laws.Int.add_def(a, b, c, d):
  PI.add_def(a, b, c, d)

def Laws.Int.mul_def(a, b, c, d):
  PI.mul_def(a, b, c, d)

def Laws.Int.abs_def(a, b):
  PI.abs_def(a, b)

def Laws.Int.eq_def(a, b, c, d):
  PI.eq_def(a, b, c, d)

def Laws.Int.le_def(a, b, c, d):
  PI.le_def(a, b, c, d)

def Laws.Int.add_comm(a, b):
  PI.Int.add_comm(a, b)

def Laws.Int.add_assoc(a, b, c):
  PI.Int.add_assoc(a, b, c)

def Laws.Int.mul_comm(a, b):
  PI.Int.mul_comm(a, b)

def Laws.Int.mul_assoc(a, b, c):
  PI.Int.mul_assoc(a, b, c)

def Laws.Int.mul_add(a, b, c):
  PI.Int.mul_add(a, b, c)

# gcd
# ---

def Laws.Nat.gcd_dvd(a, b):
  PD.gcd_dvd(a, b)

def Laws.Nat.gcd_greatest(k, a, b, ka, kb):
  PD.gcd_greatest(k, a, b, ka, kb)

def Laws.Nat.gcd_fuel(k, a, b):
  PD.gcd_fuel(k, a, b)

# Rat
# ---

def Laws.Rat.make_zero(n):
  {==}

def Laws.Rat.make_ok(n, d, nz):
  PR.make_ok(n, d, nz)

def Laws.Rat.canon_eq(a, b, ca, cb, h):
  PR.canon_eq(a, b, ca, cb, h)

def Laws.Rat.of_int_ok(n):
  PR.of_int_ok(n)

def Laws.Rat.neg_ok(a, ca):
  PR.neg_ok(a, ca)

def Laws.Rat.add_ok(a, b):
  PR.add_ok(a, b)

def Laws.Rat.sub_ok(a, b):
  PR.sub_ok(a, b)

def Laws.Rat.mul_ok(a, b):
  PR.mul_ok(a, b)

def Laws.Rat.inv_zero(d):
  {==}

def Laws.Rat.inv_ok(a, ca, nz):
  PR.inv_ok(a, ca, nz)

def Laws.Rat.div_zero(a, d):
  {==}

def Laws.Rat.div_ok(a, b, nz):
  PR.div_ok(a, b, nz)

def Laws.Rat.le_def(a, b):
  PR.le_def(a, b)

def Laws.Rat.add_comm(a, b):
  PR.add_comm(a, b)

def Laws.Rat.add_assoc(a, b, c):
  PR.add_assoc(a, b, c)

def Laws.Rat.add_zero(a, ca):
  PR.add_zero(a, ca)

def Laws.Rat.add_neg(a):
  PR.add_neg(a)

def Laws.Rat.mul_comm(a, b):
  PR.mul_comm(a, b)

def Laws.Rat.mul_assoc(a, b, c):
  PR.mul_assoc(a, b, c)

def Laws.Rat.mul_one(a, ca):
  PR.mul_one(a, ca)

def Laws.Rat.mul_add(a, b, c):
  PR.mul_add(a, b, c)

# Sums
# ----

def Laws.Stats.par_seq(l, ps):
  PS.par_seq(l, ps)

# Regression
# ----------

def Laws.fit_mismatch(k, fi, xs, ys, h):
  %Equal.sym(Bool, Nat.is_eq(List.length(&2, N.Rat, xs), List.length(&2, N.Rat, ys)), False{}, h)
    : {L.LinearRegression.fit.sizes(k, fi, _, xs, ys) == Fail{L.LengthMismatch{}} : Result<L.FitError, L.LinearRegression>}
  {==}

def Laws.fit_empty(k, fi):
  {==}

def Laws.fit_too_large(k, fi, x, xt, y, yt, len, big):
  PZ.fit_too_large(k, fi, x, xt, y, yt, len, big)

def Laws.predict_ok(k, fi, a, b, xs, small):
  PZ.predict_ok(k, fi, a, b, xs, small)

def Laws.predict_too_large(k, fi, a, b, xs, big):
  PZ.predict_too_large(k, fi, a, b, xs, big)

def Laws.fit_flat(k, x, xt, y, yt, len, small, flat):
  PRG.fit_flat(k, x, xt, y, yt, len, small, flat)

def Laws.fit_ok(k, x, xt, y, yt, len, small, spread):
  PRG.fit_ok(k, x, xt, y, yt, len, small, spread)

def Laws.fit_origin_flat(k, x, xt, y, yt, len, small, zero):
  PRG.fit_origin_flat(k, x, xt, y, yt, len, small, zero)

def Laws.fit_origin_ok(k, x, xt, y, yt, len, small, nonzero):
  PRG.fit_origin_ok(k, x, xt, y, yt, len, small, nonzero)

def Laws.normal_eq(k, xs, ys, a, b, ok):
  PLS.normal_eq(k, xs, ys, a, b, ok)

def Laws.normal_eq_origin(k, xs, ys, a, b, ok):
  PLS.normal_eq_origin(k, xs, ys, a, b, ok)

def Laws.least_squares(k, xs, ys, a, b, ok, a2, b2):
  PLS.least_squares(k, xs, ys, a, b, ok, a2, b2)

def Laws.least_squares_origin(k, xs, ys, a, b, ok, a2):
  PLS.least_squares_origin(k, xs, ys, a, b, ok, a2)

def Laws.least_squares_unique(k, xs, ys, a, b, ok, a2, b2, good):
  PLS.least_squares_unique(k, xs, ys, a, b, ok, a2, b2, good)

def Laws.least_squares_origin_unique(k, xs, ys, a, b, ok, a2, good):
  PLS.least_squares_origin_unique(k, xs, ys, a, b, ok, a2, good)
