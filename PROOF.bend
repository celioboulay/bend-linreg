import Base
import ./num.bend as N
import ./LAWS.bend as Laws
import ./p_int.bend as PI
import ./p_div.bend as PD

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
