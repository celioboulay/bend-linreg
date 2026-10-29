import Base
import ./num.bend as N
import ./linreg.bend as L
import ./p_nat.bend as PN
import ./p_int.bend as PI

# The parallel tree reduction equals the sequential fold: the tree holds
# the points in order, and Stats.add is associative with Stats.zero as unit.

# Int unit laws
# -------------

law Int.zero_add:
  for +x: N.Int
  {N.Int.add(N.Pos{0n}, x) == x : N.Int}

def Int.zero_add(x):
  match x:
    case N.Pos{m}:
      {==}
    case N.Neg{m}:
      PI.sub_nat_neg(m)

law Int.add_zero:
  for +x: N.Int
  {N.Int.add(x, N.Pos{0n}) == x : N.Int}

def Int.add_zero(x):
  match x:
    case N.Pos{m}:
      %PN.add_zero_r(m) : {N.Pos{Nat.add(m, 0n)} == N.Pos{_} : N.Int}
      {==}
    case N.Neg{m}:
      PI.sub_nat_neg(m)

# Stats is a monoid
# -----------------

law Stats.zero_add:
  for +s: L.Stats
  {L.Stats.add(L.Stats.zero(), s) == s : L.Stats}

def Stats.zero_add(s):
  match s:
    case L.Stats{n, x, y, xy, xx}:
      %Int.zero_add(n)
        : {L.Stats{N.Int.add(N.Pos{0n}, n), N.Int.add(N.Pos{0n}, x), N.Int.add(N.Pos{0n}, y), N.Int.add(N.Pos{0n}, xy), N.Int.add(N.Pos{0n}, xx)}
            == L.Stats{_, x, y, xy, xx} : L.Stats}
      %Int.zero_add(x)
        : {L.Stats{N.Int.add(N.Pos{0n}, n), N.Int.add(N.Pos{0n}, x), N.Int.add(N.Pos{0n}, y), N.Int.add(N.Pos{0n}, xy), N.Int.add(N.Pos{0n}, xx)}
            == L.Stats{N.Int.add(N.Pos{0n}, n), _, y, xy, xx} : L.Stats}
      %Int.zero_add(y)
        : {L.Stats{N.Int.add(N.Pos{0n}, n), N.Int.add(N.Pos{0n}, x), N.Int.add(N.Pos{0n}, y), N.Int.add(N.Pos{0n}, xy), N.Int.add(N.Pos{0n}, xx)}
            == L.Stats{N.Int.add(N.Pos{0n}, n), N.Int.add(N.Pos{0n}, x), _, xy, xx} : L.Stats}
      %Int.zero_add(xy)
        : {L.Stats{N.Int.add(N.Pos{0n}, n), N.Int.add(N.Pos{0n}, x), N.Int.add(N.Pos{0n}, y), N.Int.add(N.Pos{0n}, xy), N.Int.add(N.Pos{0n}, xx)}
            == L.Stats{N.Int.add(N.Pos{0n}, n), N.Int.add(N.Pos{0n}, x), N.Int.add(N.Pos{0n}, y), _, xx} : L.Stats}
      %Int.zero_add(xx)
        : {L.Stats{N.Int.add(N.Pos{0n}, n), N.Int.add(N.Pos{0n}, x), N.Int.add(N.Pos{0n}, y), N.Int.add(N.Pos{0n}, xy), N.Int.add(N.Pos{0n}, xx)}
            == L.Stats{N.Int.add(N.Pos{0n}, n), N.Int.add(N.Pos{0n}, x), N.Int.add(N.Pos{0n}, y), N.Int.add(N.Pos{0n}, xy), _} : L.Stats}
      {==}

law Stats.add_zero:
  for +s: L.Stats
  {L.Stats.add(s, L.Stats.zero()) == s : L.Stats}

def Stats.add_zero(s):
  match s:
    case L.Stats{n, x, y, xy, xx}:
      %Int.add_zero(n)
        : {L.Stats{N.Int.add(n, N.Pos{0n}), N.Int.add(x, N.Pos{0n}), N.Int.add(y, N.Pos{0n}), N.Int.add(xy, N.Pos{0n}), N.Int.add(xx, N.Pos{0n})}
            == L.Stats{_, x, y, xy, xx} : L.Stats}
      %Int.add_zero(x)
        : {L.Stats{N.Int.add(n, N.Pos{0n}), N.Int.add(x, N.Pos{0n}), N.Int.add(y, N.Pos{0n}), N.Int.add(xy, N.Pos{0n}), N.Int.add(xx, N.Pos{0n})}
            == L.Stats{N.Int.add(n, N.Pos{0n}), _, y, xy, xx} : L.Stats}
      %Int.add_zero(y)
        : {L.Stats{N.Int.add(n, N.Pos{0n}), N.Int.add(x, N.Pos{0n}), N.Int.add(y, N.Pos{0n}), N.Int.add(xy, N.Pos{0n}), N.Int.add(xx, N.Pos{0n})}
            == L.Stats{N.Int.add(n, N.Pos{0n}), N.Int.add(x, N.Pos{0n}), _, xy, xx} : L.Stats}
      %Int.add_zero(xy)
        : {L.Stats{N.Int.add(n, N.Pos{0n}), N.Int.add(x, N.Pos{0n}), N.Int.add(y, N.Pos{0n}), N.Int.add(xy, N.Pos{0n}), N.Int.add(xx, N.Pos{0n})}
            == L.Stats{N.Int.add(n, N.Pos{0n}), N.Int.add(x, N.Pos{0n}), N.Int.add(y, N.Pos{0n}), _, xx} : L.Stats}
      %Int.add_zero(xx)
        : {L.Stats{N.Int.add(n, N.Pos{0n}), N.Int.add(x, N.Pos{0n}), N.Int.add(y, N.Pos{0n}), N.Int.add(xy, N.Pos{0n}), N.Int.add(xx, N.Pos{0n})}
            == L.Stats{N.Int.add(n, N.Pos{0n}), N.Int.add(x, N.Pos{0n}), N.Int.add(y, N.Pos{0n}), N.Int.add(xy, N.Pos{0n}), _} : L.Stats}
      {==}

law Stats.add_assoc:
  for +a: L.Stats
  for +b: L.Stats
  for +c: L.Stats
  {L.Stats.add(L.Stats.add(a, b), c) == L.Stats.add(a, L.Stats.add(b, c)) : L.Stats}

def Stats.add_assoc(a, b, c):
  match a b c:
    case L.Stats{n1, x1, y1, xy1, xx1} L.Stats{n2, x2, y2, xy2, xx2} L.Stats{n3, x3, y3, xy3, xx3}:
      %PI.Int.add_assoc(n1, n2, n3)
        : {L.Stats{N.Int.add(N.Int.add(n1, n2), n3), N.Int.add(N.Int.add(x1, x2), x3), N.Int.add(N.Int.add(y1, y2), y3), N.Int.add(N.Int.add(xy1, xy2), xy3), N.Int.add(N.Int.add(xx1, xx2), xx3)}
            == L.Stats{_, N.Int.add(x1, N.Int.add(x2, x3)), N.Int.add(y1, N.Int.add(y2, y3)), N.Int.add(xy1, N.Int.add(xy2, xy3)), N.Int.add(xx1, N.Int.add(xx2, xx3))} : L.Stats}
      %PI.Int.add_assoc(x1, x2, x3)
        : {L.Stats{N.Int.add(N.Int.add(n1, n2), n3), N.Int.add(N.Int.add(x1, x2), x3), N.Int.add(N.Int.add(y1, y2), y3), N.Int.add(N.Int.add(xy1, xy2), xy3), N.Int.add(N.Int.add(xx1, xx2), xx3)}
            == L.Stats{N.Int.add(N.Int.add(n1, n2), n3), _, N.Int.add(y1, N.Int.add(y2, y3)), N.Int.add(xy1, N.Int.add(xy2, xy3)), N.Int.add(xx1, N.Int.add(xx2, xx3))} : L.Stats}
      %PI.Int.add_assoc(y1, y2, y3)
        : {L.Stats{N.Int.add(N.Int.add(n1, n2), n3), N.Int.add(N.Int.add(x1, x2), x3), N.Int.add(N.Int.add(y1, y2), y3), N.Int.add(N.Int.add(xy1, xy2), xy3), N.Int.add(N.Int.add(xx1, xx2), xx3)}
            == L.Stats{N.Int.add(N.Int.add(n1, n2), n3), N.Int.add(N.Int.add(x1, x2), x3), _, N.Int.add(xy1, N.Int.add(xy2, xy3)), N.Int.add(xx1, N.Int.add(xx2, xx3))} : L.Stats}
      %PI.Int.add_assoc(xy1, xy2, xy3)
        : {L.Stats{N.Int.add(N.Int.add(n1, n2), n3), N.Int.add(N.Int.add(x1, x2), x3), N.Int.add(N.Int.add(y1, y2), y3), N.Int.add(N.Int.add(xy1, xy2), xy3), N.Int.add(N.Int.add(xx1, xx2), xx3)}
            == L.Stats{N.Int.add(N.Int.add(n1, n2), n3), N.Int.add(N.Int.add(x1, x2), x3), N.Int.add(N.Int.add(y1, y2), y3), _, N.Int.add(xx1, N.Int.add(xx2, xx3))} : L.Stats}
      %PI.Int.add_assoc(xx1, xx2, xx3)
        : {L.Stats{N.Int.add(N.Int.add(n1, n2), n3), N.Int.add(N.Int.add(x1, x2), x3), N.Int.add(N.Int.add(y1, y2), y3), N.Int.add(N.Int.add(xy1, xy2), xy3), N.Int.add(N.Int.add(xx1, xx2), xx3)}
            == L.Stats{N.Int.add(N.Int.add(n1, n2), n3), N.Int.add(N.Int.add(x1, x2), x3), N.Int.add(N.Int.add(y1, y2), y3), N.Int.add(N.Int.add(xy1, xy2), xy3), _} : L.Stats}
      {==}

# Lists of points
# ---------------

def Pts.app(xs: +List<L.Point>, +ys: +List<L.Point>) -> +List<L.Point>:
  match xs:
    case Nil{}:
      ys
    case Con{p, t}:
      p <> Pts.app(t, ys)

law Pts.app_nil:
  for +xs: +List<L.Point>
  {Pts.app(xs, Nil{}) == xs : +List<L.Point>}

def Pts.app_nil(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{p, t}:
      %Pts.app_nil(t) : {p <> Pts.app(t, Nil{}) == p <> _ : +List<L.Point>}
      {==}

law Pts.app_assoc:
  for +xs: +List<L.Point>
  for +ys: +List<L.Point>
  for +zs: +List<L.Point>
  {Pts.app(Pts.app(xs, ys), zs) == Pts.app(xs, Pts.app(ys, zs)) : +List<L.Point>}

def Pts.app_assoc(xs, ys, zs):
  match xs:
    case Nil{}:
      {==}
    case Con{p, t}:
      %Pts.app_assoc(t, ys, zs) : {p <> Pts.app(Pts.app(t, ys), zs) == p <> _ : +List<L.Point>}
      {==}

# seq(xs ++ ys) == seq(xs) + seq(ys)
law seq_app:
  for +l: Nat
  for +xs: +List<L.Point>
  for +ys: +List<L.Point>
  {L.Stats.seq(l, Pts.app(xs, ys)) == L.Stats.add(L.Stats.seq(l, xs), L.Stats.seq(l, ys)) : L.Stats}

def seq_app(l, xs, ys):
  match xs:
    case Nil{}:
      Equal.sym(L.Stats, L.Stats.add(L.Stats.zero(), L.Stats.seq(l, ys)), L.Stats.seq(l, ys), Stats.zero_add(L.Stats.seq(l, ys)))
    case Con{p, t}:
      %Equal.sym(L.Stats, L.Stats.seq(l, Pts.app(t, ys)), L.Stats.add(L.Stats.seq(l, t), L.Stats.seq(l, ys)), seq_app(l, t, ys))
        : {L.Stats.add(L.Stats.point(l, p), _)
            == L.Stats.add(L.Stats.add(L.Stats.point(l, p), L.Stats.seq(l, t)), L.Stats.seq(l, ys)) : L.Stats}
      %Stats.add_assoc(L.Stats.point(l, p), L.Stats.seq(l, t), L.Stats.seq(l, ys))
        : {_ == L.Stats.add(L.Stats.add(L.Stats.point(l, p), L.Stats.seq(l, t)), L.Stats.seq(l, ys)) : L.Stats}
      {==}

# Trees
# -----

def Tree.flat(t: L.Tree) -> +List<L.Point>:
  match t:
    case L.TNil{}:
      Nil{}
    case L.TLeaf{p}:
      [p]
    case L.TNode{a, b}:
      Pts.app(Tree.flat(a), Tree.flat(b))

def Trees.flat(ts: +List<L.Tree>) -> +List<L.Point>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{t, r}:
      Pts.app(Tree.flat(t), Trees.flat(r))

# A tree's reduction is the fold over its points.
law stats_flat:
  for +l: Nat
  for +t: L.Tree
  {L.Tree.stats(l, t) == L.Stats.seq(l, Tree.flat(t)) : L.Stats}

def stats_flat(l, t):
  match t:
    case L.TNil{}:
      {==}
    case L.TLeaf{p}:
      Equal.sym(L.Stats, L.Stats.add(L.Stats.point(l, p), L.Stats.zero()), L.Stats.point(l, p), Stats.add_zero(L.Stats.point(l, p)))
    case L.TNode{a, b}:
      %Equal.sym(L.Stats, L.Stats.seq(l, Pts.app(Tree.flat(a), Tree.flat(b))),
          L.Stats.add(L.Stats.seq(l, Tree.flat(a)), L.Stats.seq(l, Tree.flat(b))), seq_app(l, Tree.flat(a), Tree.flat(b)))
        : {L.Stats.add(L.Tree.stats(l, a), L.Tree.stats(l, b)) == _ : L.Stats}
      %stats_flat(l, a) : {L.Stats.add(L.Tree.stats(l, a), L.Tree.stats(l, b)) == L.Stats.add(_, L.Stats.seq(l, Tree.flat(b))) : L.Stats}
      %stats_flat(l, b) : {L.Stats.add(L.Tree.stats(l, a), L.Tree.stats(l, b)) == L.Stats.add(L.Tree.stats(l, a), _) : L.Stats}
      {==}

law leaves_flat:
  for +ps: +List<L.Point>
  {Trees.flat(L.Tree.leaves(ps)) == ps : +List<L.Point>}

def leaves_flat(ps):
  match ps:
    case Nil{}:
      {==}
    case Con{p, t}:
      %leaves_flat(t) : {p <> Trees.flat(L.Tree.leaves(t)) == p <> _ : +List<L.Point>}
      {==}

law pairs_flat:
  for +ts: +List<L.Tree>
  {Trees.flat(L.Tree.pairs(ts)) == Trees.flat(ts) : +List<L.Point>}

def pairs_flat(ts):
  match ts:
    case Nil{}:
      {==}
    case Con{a, Nil{}}:
      {==}
    case Con{a, Con{b, t}}:
      %pairs_flat(t)
        : {Pts.app(Pts.app(Tree.flat(a), Tree.flat(b)), Trees.flat(L.Tree.pairs(t)))
            == Pts.app(Tree.flat(a), Pts.app(Tree.flat(b), _)) : +List<L.Point>}
      Pts.app_assoc(Tree.flat(a), Tree.flat(b), Trees.flat(L.Tree.pairs(t)))

law rounds_flat:
  for +f: Nat
  for +ts: +List<L.Tree>
  {Trees.flat(L.Tree.rounds(f, ts)) == Trees.flat(ts) : +List<L.Point>}

def rounds_flat(f, ts):
  match f:
    case 0n:
      {==}
    case 1n+g:
      Equal.trans(+List<L.Point>, Trees.flat(L.Tree.rounds(g, L.Tree.pairs(ts))), Trees.flat(L.Tree.pairs(ts)), Trees.flat(ts),
        rounds_flat(g, L.Tree.pairs(ts)), pairs_flat(ts))

law join_flat:
  for +ts: +List<L.Tree>
  {Tree.flat(L.Tree.join(ts)) == Trees.flat(ts) : +List<L.Point>}

def join_flat(ts):
  match ts:
    case Nil{}:
      {==}
    case Con{t, Nil{}}:
      Equal.sym(+List<L.Point>, Pts.app(Tree.flat(t), Nil{}), Tree.flat(t), Pts.app_nil(Tree.flat(t)))
    case Con{t, Con{u, v}}:
      %join_flat(u <> v) : {Pts.app(Tree.flat(t), Tree.flat(L.Tree.join(u <> v))) == Pts.app(Tree.flat(t), _) : +List<L.Point>}
      {==}

law par_seq:
  for +l: Nat
  for +ps: +List<L.Point>
  {L.Stats.par(l, ps) == L.Stats.seq(l, ps) : L.Stats}

def par_seq(l, ps):
  %leaves_flat(ps) : {L.Stats.par(l, ps) == L.Stats.seq(l, _) : L.Stats}
  %rounds_flat(List.length(&2, L.Point, ps), L.Tree.leaves(ps))
    : {L.Stats.par(l, ps) == L.Stats.seq(l, _) : L.Stats}
  %join_flat(L.Tree.rounds(List.length(&2, L.Point, ps), L.Tree.leaves(ps)))
    : {L.Stats.par(l, ps) == L.Stats.seq(l, _) : L.Stats}
  %stats_flat(l, L.Tree.join(L.Tree.rounds(List.length(&2, L.Point, ps), L.Tree.leaves(ps))))
    : {L.Stats.par(l, ps) == _ : L.Stats}
  {==}
