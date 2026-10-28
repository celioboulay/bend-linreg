import Base

# Nat: semiring laws, proven from Base's definitions.

law add_zero_r:
  for +a: Nat
  {Nat.add(a, 0n) == a : Nat}

def add_zero_r(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_zero_r(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

law add_succ_r:
  for +a: Nat
  for +b: Nat
  {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}

def add_succ_r(a, b):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ_r(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

law add_comm:
  for +a: Nat
  for +b: Nat
  {Nat.add(a, b) == Nat.add(b, a) : Nat}

def add_comm(a, b):
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, add_zero_r(b))
    case 1n+p:
      %Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), add_succ_r(b, p)) : {1n+Nat.add(p, b) == _ : Nat}
      %add_comm(p, b) : {1n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

law add_assoc:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}

def add_assoc(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

# a + (b + c) == b + (a + c)
law add_left_comm:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}

def add_left_comm(a, b, c):
  %add_assoc(b, a, c) : {Nat.add(a, Nat.add(b, c)) == _ : Nat}
  %add_comm(a, b) : {Nat.add(a, Nat.add(b, c)) == Nat.add(_, c) : Nat}
  %add_assoc(a, b, c) : {_ == Nat.add(Nat.add(a, b), c) : Nat}
  {==}

law mul_zero_r:
  for +a: Nat
  {Nat.mul(a, 0n) == 0n : Nat}

def mul_zero_r(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      mul_zero_r(p)

law mul_succ_r:
  for +a: Nat
  for +b: Nat
  {Nat.mul(a, 1n+b) == Nat.add(a, Nat.mul(a, b)) : Nat}

def mul_succ_r(a, b):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.mul(p, 1n+b), Nat.add(p, Nat.mul(p, b)), mul_succ_r(p, b))
        : {1n+Nat.add(b, _) == 1n+Nat.add(p, Nat.add(b, Nat.mul(p, b))) : Nat}
      %add_left_comm(b, p, Nat.mul(p, b)) : {1n+Nat.add(b, Nat.add(p, Nat.mul(p, b))) == 1n+_ : Nat}
      {==}

law mul_one_r:
  for +a: Nat
  {Nat.mul(a, 1n) == a : Nat}

def mul_one_r(a):
  %Equal.sym(Nat, Nat.mul(a, 1n), Nat.add(a, Nat.mul(a, 0n)), mul_succ_r(a, 0n)) : {_ == a : Nat}
  %Equal.sym(Nat, Nat.mul(a, 0n), 0n, mul_zero_r(a)) : {Nat.add(a, _) == a : Nat}
  add_zero_r(a)

law mul_comm:
  for +a: Nat
  for +b: Nat
  {Nat.mul(a, b) == Nat.mul(b, a) : Nat}

def mul_comm(a, b):
  match a:
    case 0n:
      Equal.sym(Nat, Nat.mul(b, 0n), 0n, mul_zero_r(b))
    case 1n+p:
      %Equal.sym(Nat, Nat.mul(b, 1n+p), Nat.add(b, Nat.mul(b, p)), mul_succ_r(b, p))
        : {Nat.add(b, Nat.mul(p, b)) == _ : Nat}
      %mul_comm(p, b) : {Nat.add(b, Nat.mul(p, b)) == Nat.add(b, _) : Nat}
      {==}

# (a + b) c == a c + b c
law mul_add_r:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.mul(Nat.add(a, b), c) == Nat.add(Nat.mul(a, c), Nat.mul(b, c)) : Nat}

def mul_add_r(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(Nat.add(c, Nat.mul(p, c)), Nat.mul(b, c)), Nat.add(c, Nat.add(Nat.mul(p, c), Nat.mul(b, c))),
          add_assoc(c, Nat.mul(p, c), Nat.mul(b, c)))
        : {Nat.add(c, Nat.mul(Nat.add(p, b), c)) == _ : Nat}
      %mul_add_r(p, b, c) : {Nat.add(c, Nat.mul(Nat.add(p, b), c)) == Nat.add(c, _) : Nat}
      {==}

# a (b + c) == a b + a c
law mul_add_l:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.mul(a, Nat.add(b, c)) == Nat.add(Nat.mul(a, b), Nat.mul(a, c)) : Nat}

def mul_add_l(a, b, c):
  %mul_comm(Nat.add(b, c), a) : {_ == Nat.add(Nat.mul(a, b), Nat.mul(a, c)) : Nat}
  %mul_comm(b, a) : {Nat.mul(Nat.add(b, c), a) == Nat.add(_, Nat.mul(a, c)) : Nat}
  %mul_comm(c, a) : {Nat.mul(Nat.add(b, c), a) == Nat.add(Nat.mul(b, a), _) : Nat}
  mul_add_r(b, c, a)

law mul_assoc:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.mul(Nat.mul(a, b), c) == Nat.mul(a, Nat.mul(b, c)) : Nat}

def mul_assoc(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %mul_assoc(p, b, c) : {Nat.mul(Nat.add(b, Nat.mul(p, b)), c) == Nat.add(Nat.mul(b, c), _) : Nat}
      mul_add_r(b, Nat.mul(p, b), c)

# a (b c) == b (a c)
law mul_left_comm:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.mul(a, Nat.mul(b, c)) == Nat.mul(b, Nat.mul(a, c)) : Nat}

def mul_left_comm(a, b, c):
  %mul_assoc(b, a, c) : {Nat.mul(a, Nat.mul(b, c)) == _ : Nat}
  %mul_comm(a, b) : {Nat.mul(a, Nat.mul(b, c)) == Nat.mul(_, c) : Nat}
  %mul_assoc(a, b, c) : {_ == Nat.mul(Nat.mul(a, b), c) : Nat}
  {==}

# (a b) (c d) == (a c) (b d)
law mul_mul_swap:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  {Nat.mul(Nat.mul(a, b), Nat.mul(c, d)) == Nat.mul(Nat.mul(a, c), Nat.mul(b, d)) : Nat}

def mul_mul_swap(a, b, c, d):
  %Equal.sym(Nat, Nat.mul(Nat.mul(a, c), Nat.mul(b, d)), Nat.mul(a, Nat.mul(c, Nat.mul(b, d))),
      mul_assoc(a, c, Nat.mul(b, d)))
    : {Nat.mul(Nat.mul(a, b), Nat.mul(c, d)) == _ : Nat}
  %mul_left_comm(b, c, d) : {Nat.mul(Nat.mul(a, b), Nat.mul(c, d)) == Nat.mul(a, _) : Nat}
  mul_assoc(a, b, Nat.mul(c, d))
