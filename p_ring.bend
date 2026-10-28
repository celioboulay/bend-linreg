import Base
import ./p_nat.bend as PN

# A proven normalizer for Nat polynomial identities. An expression (Ex) is
# turned into a sorted sum of monomials; Ring.eq says two expressions are
# equal whenever their normal forms are, which {==} checks by computation:
#   Ring.eq(e1, e2, env, {==}) : {Ex.eval(e1, env) == Ex.eval(e2, env) : Nat}
# Only soundness is proven (normalizing keeps the value), so a pair of equal
# expressions the normalizer fails to identify is rejected, never accepted.

type Ex is Data:
  EVar{i: Nat}
  ENum{n: Nat}
  EAdd{a: Ex, b: Ex}
  EMul{a: Ex, b: Ex}

def Env.get(env: +List<Nat>, +i: Nat) -> Nat:
  match env:
    case Nil{}:
      0n
    case Con{h, t}:
      match i:
        case 0n:
          h
        case 1n+j:
          Env.get(t, j)

def Ex.eval(e: Ex, +env: +List<Nat>) -> Nat:
  match e:
    case EVar{i}:
      Env.get(env, i)
    case ENum{n}:
      n
    case EAdd{a, b}:
      Nat.add(Ex.eval(a, env), Ex.eval(b, env))
    case EMul{a, b}:
      Nat.mul(Ex.eval(a, env), Ex.eval(b, env))

# Monomials: a coefficient times a sorted list of variables.

def Vars.eval(vs: +List<Nat>, +env: +List<Nat>) -> Nat:
  match vs:
    case Nil{}:
      1n
    case Con{v, t}:
      Nat.mul(Env.get(env, v), Vars.eval(t, env))

def Vars.pick(c: Bool, a: +List<Nat>, b: +List<Nat>) -> +List<Nat>:
  match c:
    case True{}:
      a
    case False{}:
      b

def Vars.ins(+x: Nat, vs: +List<Nat>) -> +List<Nat>:
  match vs:
    case Nil{}:
      [x]
    case Con{+v, +t}:
      Vars.pick(Nat.is_le(x, v), x <> v <> t, v <> Vars.ins(x, t))

def Vars.mul(xs: +List<Nat>, +ys: +List<Nat>) -> +List<Nat>:
  match xs:
    case Nil{}:
      ys
    case Con{x, t}:
      Vars.ins(x, Vars.mul(t, ys))

def Cmp.then(c: Cmp, d: Cmp) -> Cmp:
  match c:
    case EQ{}:
      d
    case LT{}:
      LT{}
    case GT{}:
      GT{}

def Vars.cmp(xs: +List<Nat>, ys: +List<Nat>) -> Cmp:
  match xs ys:
    case Nil{} Nil{}:
      EQ{}
    case Nil{} Con{y, t}:
      LT{}
    case Con{x, t} Nil{}:
      GT{}
    case Con{x, xt} Con{y, yt}:
      Cmp.then(Nat.cmp(x, y), Vars.cmp(xt, yt))

type Mono is Data:
  Mono{c: Nat, vs: +List<Nat>}

# Polynomials: monomials sorted by their variables, coefficients nonzero.

def Poly.eval(p: +List<Mono>, +env: +List<Nat>) -> Nat:
  match p:
    case Nil{}:
      0n
    case Con{Mono{c, vs}, t}:
      Nat.add(Nat.mul(c, Vars.eval(vs, env)), Poly.eval(t, env))

def Poly.pick(c: Cmp, lt: +List<Mono>, eq: +List<Mono>, gt: +List<Mono>) -> +List<Mono>:
  match c:
    case LT{}:
      lt
    case EQ{}:
      eq
    case GT{}:
      gt

# Adds c vs into q, merging it with a monomial of the same variables.
def Poly.ins(+c: Nat, +vs: +List<Nat>, q: +List<Mono>) -> +List<Mono>:
  match q:
    case Nil{}:
      [Mono{c, vs}]
    case Con{Mono{+d, +ws}, +t}:
      Poly.pick(Vars.cmp(vs, ws),
        Mono{c, vs} <> Mono{d, ws} <> t,
        Mono{Nat.add(c, d), vs} <> t,
        Mono{d, ws} <> Poly.ins(c, vs, t))

def Poly.add(p: +List<Mono>, +q: +List<Mono>) -> +List<Mono>:
  match p:
    case Nil{}:
      q
    case Con{Mono{c, vs}, t}:
      Poly.ins(c, vs, Poly.add(t, q))

# (c vs) * q
def Poly.scale(+c: Nat, +vs: +List<Nat>, q: +List<Mono>) -> +List<Mono>:
  match q:
    case Nil{}:
      Nil{}
    case Con{Mono{d, ws}, t}:
      Poly.ins(Nat.mul(c, d), Vars.mul(vs, ws), Poly.scale(c, vs, t))

def Poly.mul(p: +List<Mono>, +q: +List<Mono>) -> +List<Mono>:
  match p:
    case Nil{}:
      Nil{}
    case Con{Mono{c, vs}, t}:
      Poly.add(Poly.scale(c, vs, q), Poly.mul(t, q))

def Ex.norm(e: Ex) -> +List<Mono>:
  match e:
    case EVar{i}:
      [Mono{1n, [i]}]
    case ENum{0n}:
      Nil{}
    case ENum{1n+k}:
      [Mono{1n+k, Nil{}}]
    case EAdd{a, b}:
      Poly.add(Ex.norm(a), Ex.norm(b))
    case EMul{a, b}:
      Poly.mul(Ex.norm(a), Ex.norm(b))

# Soundness
# ---------

def Cmp.eqd(c: Cmp) -> Type:
  match c:
    case EQ{}:
      Unit
    case LT{}:
      Empty
    case GT{}:
      Empty

law Cmp.eq_lt:
  for e: {EQ{} == LT{} : Cmp}
  Empty

def Cmp.eq_lt(e):
  %e : Cmp.eqd(_)
  Unit{}

law Cmp.eq_gt:
  for e: {EQ{} == GT{} : Cmp}
  Empty

def Cmp.eq_gt(e):
  %e : Cmp.eqd(_)
  Unit{}

law Nat.cmp_eq:
  for +x: Nat
  for +y: Nat
  for e: {EQ{} == Nat.cmp(x, y) : Cmp}
  {x == y : Nat}

def Nat.cmp_eq(x, y, e):
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Empty.absurd({0n == 1n+q : Nat}, Cmp.eq_lt(e))
    case 1n+p 0n:
      Empty.absurd({1n+p == 0n : Nat}, Cmp.eq_gt(e))
    case 1n+p 1n+q:
      %Nat.cmp_eq(p, q, e) : {1n+p == 1n+_ : Nat}
      {==}

law Cmp.then_eq_l:
  for c: Cmp
  for d: Cmp
  for e: {EQ{} == Cmp.then(c, d) : Cmp}
  {EQ{} == c : Cmp}

def Cmp.then_eq_l(c, d, e):
  match c:
    case EQ{}:
      {==}
    case LT{}:
      Empty.absurd({EQ{} == LT{} : Cmp}, Cmp.eq_lt(e))
    case GT{}:
      Empty.absurd({EQ{} == GT{} : Cmp}, Cmp.eq_gt(e))

law Cmp.then_eq_r:
  for c: Cmp
  for d: Cmp
  for e: {EQ{} == Cmp.then(c, d) : Cmp}
  {EQ{} == d : Cmp}

def Cmp.then_eq_r(c, d, e):
  match c:
    case EQ{}:
      e
    case LT{}:
      Empty.absurd({EQ{} == d : Cmp}, Cmp.eq_lt(e))
    case GT{}:
      Empty.absurd({EQ{} == d : Cmp}, Cmp.eq_gt(e))

law Vars.cmp_eq:
  for +xs: +List<Nat>
  for +ys: +List<Nat>
  for +e: {EQ{} == Vars.cmp(xs, ys) : Cmp}
  {xs == ys : +List<Nat>}

def Vars.cmp_eq(xs, ys, e):
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, t}:
      Empty.absurd({Nil{} == y <> t : +List<Nat>}, Cmp.eq_lt(e))
    case Con{x, t} Nil{}:
      Empty.absurd({x <> t == Nil{} : +List<Nat>}, Cmp.eq_gt(e))
    case Con{x, xt} Con{y, yt}:
      %Nat.cmp_eq(x, y, Cmp.then_eq_l(Nat.cmp(x, y), Vars.cmp(xt, yt), e))
        : {x <> xt == _ <> yt : +List<Nat>}
      %Vars.cmp_eq(xt, yt, Cmp.then_eq_r(Nat.cmp(x, y), Vars.cmp(xt, yt), e))
        : {x <> xt == x <> _ : +List<Nat>}
      {==}

law Vars.ins_ok.go:
  for b: Bool
  for +x: Nat
  for +v: Nat
  for +t: +List<Nat>
  for +env: +List<Nat>
  for ih: {Nat.mul(Env.get(env, x), Vars.eval(t, env)) == Vars.eval(Vars.ins(x, t), env) : Nat}
  {Nat.mul(Env.get(env, x), Vars.eval(v <> t, env))
    == Vars.eval(Vars.pick(b, x <> v <> t, v <> Vars.ins(x, t)), env) : Nat}

def Vars.ins_ok.go(b, x, v, t, env, ih):
  match b:
    case True{}:
      {==}
    case False{}:
      %ih : {Nat.mul(Env.get(env, x), Nat.mul(Env.get(env, v), Vars.eval(t, env)))
              == Nat.mul(Env.get(env, v), _) : Nat}
      PN.mul_left_comm(Env.get(env, x), Env.get(env, v), Vars.eval(t, env))

law Vars.ins_ok:
  for +x: Nat
  for +vs: +List<Nat>
  for +env: +List<Nat>
  {Nat.mul(Env.get(env, x), Vars.eval(vs, env)) == Vars.eval(Vars.ins(x, vs), env) : Nat}

def Vars.ins_ok(x, vs, env):
  match vs:
    case Nil{}:
      {==}
    case Con{v, t}:
      Vars.ins_ok.go(Nat.is_le(x, v), x, v, t, env, Vars.ins_ok(x, t, env))

law Vars.mul_ok:
  for +xs: +List<Nat>
  for +ys: +List<Nat>
  for +env: +List<Nat>
  {Nat.mul(Vars.eval(xs, env), Vars.eval(ys, env)) == Vars.eval(Vars.mul(xs, ys), env) : Nat}

def Vars.mul_ok(xs, ys, env):
  match xs:
    case Nil{}:
      PN.add_zero_r(Vars.eval(ys, env))
    case Con{x, t}:
      %Vars.ins_ok(x, Vars.mul(t, ys), env)
        : {Nat.mul(Nat.mul(Env.get(env, x), Vars.eval(t, env)), Vars.eval(ys, env)) == _ : Nat}
      %Vars.mul_ok(t, ys, env)
        : {Nat.mul(Nat.mul(Env.get(env, x), Vars.eval(t, env)), Vars.eval(ys, env))
            == Nat.mul(Env.get(env, x), _) : Nat}
      PN.mul_assoc(Env.get(env, x), Vars.eval(t, env), Vars.eval(ys, env))

law Poly.ins_ok.go:
  for k: Cmp
  for +c: Nat
  for +vs: +List<Nat>
  for +d: Nat
  for +ws: +List<Nat>
  for +t: +List<Mono>
  for +env: +List<Nat>
  for ek: {k == Vars.cmp(vs, ws) : Cmp}
  for ih: {Nat.add(Nat.mul(c, Vars.eval(vs, env)), Poly.eval(t, env)) == Poly.eval(Poly.ins(c, vs, t), env) : Nat}
  {Nat.add(Nat.mul(c, Vars.eval(vs, env)), Nat.add(Nat.mul(d, Vars.eval(ws, env)), Poly.eval(t, env)))
    == Poly.eval(Poly.pick(k,
         Mono{c, vs} <> Mono{d, ws} <> t,
         Mono{Nat.add(c, d), vs} <> t,
         Mono{d, ws} <> Poly.ins(c, vs, t)), env) : Nat}

def Poly.ins_ok.go(k, c, vs, d, ws, t, env, ek, ih):
  match k:
    case LT{}:
      {==}
    case EQ{}:
      %Vars.cmp_eq(vs, ws, ek)
        : {Nat.add(Nat.mul(c, Vars.eval(vs, env)), Nat.add(Nat.mul(d, Vars.eval(_, env)), Poly.eval(t, env)))
            == Nat.add(Nat.mul(Nat.add(c, d), Vars.eval(vs, env)), Poly.eval(t, env)) : Nat}
      %Equal.sym(Nat, Nat.mul(Nat.add(c, d), Vars.eval(vs, env)),
          Nat.add(Nat.mul(c, Vars.eval(vs, env)), Nat.mul(d, Vars.eval(vs, env))),
          PN.mul_add_r(c, d, Vars.eval(vs, env)))
        : {Nat.add(Nat.mul(c, Vars.eval(vs, env)), Nat.add(Nat.mul(d, Vars.eval(vs, env)), Poly.eval(t, env)))
            == Nat.add(_, Poly.eval(t, env)) : Nat}
      Equal.sym(Nat,
        Nat.add(Nat.add(Nat.mul(c, Vars.eval(vs, env)), Nat.mul(d, Vars.eval(vs, env))), Poly.eval(t, env)),
        Nat.add(Nat.mul(c, Vars.eval(vs, env)), Nat.add(Nat.mul(d, Vars.eval(vs, env)), Poly.eval(t, env))),
        PN.add_assoc(Nat.mul(c, Vars.eval(vs, env)), Nat.mul(d, Vars.eval(vs, env)), Poly.eval(t, env)))
    case GT{}:
      %ih : {Nat.add(Nat.mul(c, Vars.eval(vs, env)), Nat.add(Nat.mul(d, Vars.eval(ws, env)), Poly.eval(t, env)))
              == Nat.add(Nat.mul(d, Vars.eval(ws, env)), _) : Nat}
      PN.add_left_comm(Nat.mul(c, Vars.eval(vs, env)), Nat.mul(d, Vars.eval(ws, env)), Poly.eval(t, env))

law Poly.ins_ok:
  for +c: Nat
  for +vs: +List<Nat>
  for +q: +List<Mono>
  for +env: +List<Nat>
  {Nat.add(Nat.mul(c, Vars.eval(vs, env)), Poly.eval(q, env)) == Poly.eval(Poly.ins(c, vs, q), env) : Nat}

def Poly.ins_ok(c, vs, q, env):
  match q:
    case Nil{}:
      {==}
    case Con{Mono{d, ws}, t}:
      Poly.ins_ok.go(Vars.cmp(vs, ws), c, vs, d, ws, t, env, {==}, Poly.ins_ok(c, vs, t, env))

law Poly.add_ok:
  for +p: +List<Mono>
  for +q: +List<Mono>
  for +env: +List<Nat>
  {Nat.add(Poly.eval(p, env), Poly.eval(q, env)) == Poly.eval(Poly.add(p, q), env) : Nat}

def Poly.add_ok(p, q, env):
  match p:
    case Nil{}:
      {==}
    case Con{Mono{c, vs}, t}:
      %Poly.ins_ok(c, vs, Poly.add(t, q), env)
        : {Nat.add(Nat.add(Nat.mul(c, Vars.eval(vs, env)), Poly.eval(t, env)), Poly.eval(q, env)) == _ : Nat}
      %Poly.add_ok(t, q, env)
        : {Nat.add(Nat.add(Nat.mul(c, Vars.eval(vs, env)), Poly.eval(t, env)), Poly.eval(q, env))
            == Nat.add(Nat.mul(c, Vars.eval(vs, env)), _) : Nat}
      PN.add_assoc(Nat.mul(c, Vars.eval(vs, env)), Poly.eval(t, env), Poly.eval(q, env))

law Poly.scale_ok:
  for +c: Nat
  for +vs: +List<Nat>
  for +q: +List<Mono>
  for +env: +List<Nat>
  {Nat.mul(Nat.mul(c, Vars.eval(vs, env)), Poly.eval(q, env)) == Poly.eval(Poly.scale(c, vs, q), env) : Nat}

def Poly.scale_ok(c, vs, q, env):
  match q:
    case Nil{}:
      PN.mul_zero_r(Nat.mul(c, Vars.eval(vs, env)))
    case Con{Mono{d, ws}, t}:
      %Poly.ins_ok(Nat.mul(c, d), Vars.mul(vs, ws), Poly.scale(c, vs, t), env)
        : {Nat.mul(Nat.mul(c, Vars.eval(vs, env)), Nat.add(Nat.mul(d, Vars.eval(ws, env)), Poly.eval(t, env))) == _ : Nat}
      %Vars.mul_ok(vs, ws, env)
        : {Nat.mul(Nat.mul(c, Vars.eval(vs, env)), Nat.add(Nat.mul(d, Vars.eval(ws, env)), Poly.eval(t, env)))
            == Nat.add(Nat.mul(Nat.mul(c, d), _), Poly.eval(Poly.scale(c, vs, t), env)) : Nat}
      %Poly.scale_ok(c, vs, t, env)
        : {Nat.mul(Nat.mul(c, Vars.eval(vs, env)), Nat.add(Nat.mul(d, Vars.eval(ws, env)), Poly.eval(t, env)))
            == Nat.add(Nat.mul(Nat.mul(c, d), Nat.mul(Vars.eval(vs, env), Vars.eval(ws, env))), _) : Nat}
      %Equal.sym(Nat,
          Nat.mul(Nat.mul(c, Vars.eval(vs, env)), Nat.add(Nat.mul(d, Vars.eval(ws, env)), Poly.eval(t, env))),
          Nat.add(Nat.mul(Nat.mul(c, Vars.eval(vs, env)), Nat.mul(d, Vars.eval(ws, env))),
                  Nat.mul(Nat.mul(c, Vars.eval(vs, env)), Poly.eval(t, env))),
          PN.mul_add_l(Nat.mul(c, Vars.eval(vs, env)), Nat.mul(d, Vars.eval(ws, env)), Poly.eval(t, env)))
        : {_ == Nat.add(Nat.mul(Nat.mul(c, d), Nat.mul(Vars.eval(vs, env), Vars.eval(ws, env))),
                        Nat.mul(Nat.mul(c, Vars.eval(vs, env)), Poly.eval(t, env))) : Nat}
      %PN.mul_mul_swap(c, Vars.eval(vs, env), d, Vars.eval(ws, env))
        : {Nat.add(Nat.mul(Nat.mul(c, Vars.eval(vs, env)), Nat.mul(d, Vars.eval(ws, env))),
                   Nat.mul(Nat.mul(c, Vars.eval(vs, env)), Poly.eval(t, env)))
            == Nat.add(_, Nat.mul(Nat.mul(c, Vars.eval(vs, env)), Poly.eval(t, env))) : Nat}
      {==}

law Poly.mul_ok:
  for +p: +List<Mono>
  for +q: +List<Mono>
  for +env: +List<Nat>
  {Nat.mul(Poly.eval(p, env), Poly.eval(q, env)) == Poly.eval(Poly.mul(p, q), env) : Nat}

def Poly.mul_ok(p, q, env):
  match p:
    case Nil{}:
      {==}
    case Con{Mono{c, vs}, t}:
      %Poly.add_ok(Poly.scale(c, vs, q), Poly.mul(t, q), env)
        : {Nat.mul(Nat.add(Nat.mul(c, Vars.eval(vs, env)), Poly.eval(t, env)), Poly.eval(q, env)) == _ : Nat}
      %Poly.scale_ok(c, vs, q, env)
        : {Nat.mul(Nat.add(Nat.mul(c, Vars.eval(vs, env)), Poly.eval(t, env)), Poly.eval(q, env))
            == Nat.add(_, Poly.eval(Poly.mul(t, q), env)) : Nat}
      %Poly.mul_ok(t, q, env)
        : {Nat.mul(Nat.add(Nat.mul(c, Vars.eval(vs, env)), Poly.eval(t, env)), Poly.eval(q, env))
            == Nat.add(Nat.mul(Nat.mul(c, Vars.eval(vs, env)), Poly.eval(q, env)), _) : Nat}
      PN.mul_add_r(Nat.mul(c, Vars.eval(vs, env)), Poly.eval(t, env), Poly.eval(q, env))

law Ex.norm_ok:
  for +e: Ex
  for +env: +List<Nat>
  {Ex.eval(e, env) == Poly.eval(Ex.norm(e), env) : Nat}

def Ex.norm_ok(e, env):
  match e:
    case EVar{i}:
      %Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(Env.get(env, i), 1n), 0n), 0n), Nat.add(Nat.mul(Env.get(env, i), 1n), 0n),
          PN.add_zero_r(Nat.add(Nat.mul(Env.get(env, i), 1n), 0n)))
        : {Env.get(env, i) == _ : Nat}
      %Equal.sym(Nat, Nat.add(Nat.mul(Env.get(env, i), 1n), 0n), Nat.mul(Env.get(env, i), 1n),
          PN.add_zero_r(Nat.mul(Env.get(env, i), 1n)))
        : {Env.get(env, i) == _ : Nat}
      Equal.sym(Nat, Nat.mul(Env.get(env, i), 1n), Env.get(env, i), PN.mul_one_r(Env.get(env, i)))
    case ENum{0n}:
      {==}
    case ENum{1n+k}:
      %Equal.sym(Nat, Nat.add(Nat.mul(1n+k, 1n), 0n), Nat.mul(1n+k, 1n), PN.add_zero_r(Nat.mul(1n+k, 1n)))
        : {1n+k == _ : Nat}
      Equal.sym(Nat, Nat.mul(1n+k, 1n), 1n+k, PN.mul_one_r(1n+k))
    case EAdd{a, b}:
      %Poly.add_ok(Ex.norm(a), Ex.norm(b), env)
        : {Nat.add(Ex.eval(a, env), Ex.eval(b, env)) == _ : Nat}
      %Ex.norm_ok(a, env) : {Nat.add(Ex.eval(a, env), Ex.eval(b, env)) == Nat.add(_, Poly.eval(Ex.norm(b), env)) : Nat}
      %Ex.norm_ok(b, env) : {Nat.add(Ex.eval(a, env), Ex.eval(b, env)) == Nat.add(Ex.eval(a, env), _) : Nat}
      {==}
    case EMul{a, b}:
      %Poly.mul_ok(Ex.norm(a), Ex.norm(b), env)
        : {Nat.mul(Ex.eval(a, env), Ex.eval(b, env)) == _ : Nat}
      %Ex.norm_ok(a, env) : {Nat.mul(Ex.eval(a, env), Ex.eval(b, env)) == Nat.mul(_, Poly.eval(Ex.norm(b), env)) : Nat}
      %Ex.norm_ok(b, env) : {Nat.mul(Ex.eval(a, env), Ex.eval(b, env)) == Nat.mul(Ex.eval(a, env), _) : Nat}
      {==}

# Two expressions with the same normal form have the same value.
law Ring.eq:
  for +e1: Ex
  for +e2: Ex
  for +env: +List<Nat>
  for h: {Ex.norm(e1) == Ex.norm(e2) : +List<Mono>}
  {Ex.eval(e1, env) == Ex.eval(e2, env) : Nat}

def Ring.eq(e1, e2, env, h):
  %Equal.sym(Nat, Ex.eval(e2, env), Poly.eval(Ex.norm(e2), env), Ex.norm_ok(e2, env))
    : {Ex.eval(e1, env) == _ : Nat}
  %h : {Ex.eval(e1, env) == Poly.eval(_, env) : Nat}
  Ex.norm_ok(e1, env)
