module Matmul.Strassen
open Matmul.Matrix
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.Tactics.V2
open FStar.Mul
open FStar.FunctionalExtensionality
module SZ = FStar.SizeT
module R = Pulse.Lib.Reference

type matrix_ref = array r

let upd #m #n (a : matrix m n) (i : Fin.under m) (j : Fin.under n) (x : r) : matrix m n =
  mk (fun i' j' -> if i = i' && j = j' then x else a i' j')

let of_col_maj (m n : nat) (s: Seq.seq r { Seq.length s == m*n }) : matrix m n =
  mk (fun i j ->
    assert (n*i <= n*(m-1));
    Seq.index s (n*i + j))

let pts_to_matrix (p: matrix_ref) (#[exact (`1.0R)] pr:perm) (m: SZ.t) (n: SZ.t) (a: matrix (SZ.v m) (SZ.v n)) : vprop =
  exists* (buf : Seq.seq r).
    pts_to p buf ** pure (Seq.length buf == SZ.v m * SZ.v n /\ of_col_maj (SZ.v m) (SZ.v n) buf == a)

```pulse
fn matrix_idx (p: matrix_ref) #pr (m : SZ.t) (n : SZ.t) (i : SZ.t { SZ.v i < SZ.v m }) (j : SZ.t { SZ.v j < SZ.v n }) (#a: erased (matrix (SZ.v m) (SZ.v n)))
  requires pts_to_matrix p #pr m n a
  returns x:r
  ensures pure (x == reveal a (SZ.v i) (SZ.v j)) ** pts_to_matrix p #pr m n a
{
  unfold pts_to_matrix p #pr m n a;
  pts_to_len p;
  assert pure (SZ.v n * SZ.v i + SZ.v j < SZ.v n * (SZ.v i + 1));
  let x = p.((n `SZ.mul` i) `SZ.add` j);
  fold pts_to_matrix p #pr m n a;
  x;
}
```

let col_maj_idx_inj () :
  squash (forall (n i1 j1 i2 j2 : nat). {:pattern (n*i1 + j1 == n*i2 + j2)}
    (j1 < n /\ j2 < n /\ n*i1 + j1 == n*i2 + j2) ==> (i1 == i2 /\ j1 == j2)) = admit ()

let of_col_maj_upd m n (buf: Seq.seq r { Seq.length buf == m*n }) (i: nat { i < m }) (j: nat { j < n }) (y: r) :
    Lemma (assert (n*i+j < n*(i+1));
      of_col_maj _ _ (Seq.upd buf (n*i+j) y) == upd (of_col_maj m n buf) i j y) =
  admit ()

```pulse
fn matrix_upd (p: matrix_ref) (m : SZ.t) (n : SZ.t) (i : SZ.t { SZ.v i < SZ.v m }) (j : SZ.t { SZ.v j < SZ.v n }) (#a: erased (matrix (SZ.v m) (SZ.v n))) (y: r)
  requires pts_to_matrix p m n a
  returns _: unit
  ensures pts_to_matrix p m n (upd a (SZ.v i) (SZ.v j) y)
{
  unfold pts_to_matrix p m n a;
  pts_to_len p;
  assert pure (SZ.v n * SZ.v i + SZ.v j < SZ.v n * (SZ.v i + 1));
  with buf. assert pts_to p buf;
  p.((n `SZ.mul` i) `SZ.add` j) <- y;
  of_col_maj_upd (SZ.v m) (SZ.v n) buf (SZ.v i) (SZ.v j) y;
  fold pts_to_matrix p m n (upd a (SZ.v i) (SZ.v j) y);
}
```

// TODO: does not work if inlined?
let compute_dot_elem_inv
    (#m #n #k : SZ.t)
    (i : SZ.t { SZ.v i < SZ.v m })
    (j : SZ.t { SZ.v j < SZ.v k })
    (a: erased (matrix (SZ.v m) (SZ.v n)))
    (b: erased (matrix (SZ.v n) (SZ.v k)))
    (vacc : r) (vl : SZ.t ) : prop =
  SZ.v vl <= SZ.v n /\
    vacc == bigsum 0 (SZ.v vl) (dot_summand a b (SZ.v i) (SZ.v j))

let rec bigsum_rec_left (m : nat) (n : nat {m <= n}) (f : (i:nat { m <= i /\ i < n } -> r)) :
    Lemma (ensures m <> n ==> bigsum m n f == f m + bigsum (m+1) n f) (decreases n) =
  if m = n || m + 1 = n then () else
  (bigsum_rec_left m (n-1) f; bigsum_rec_left (m+1) (n-1) f)

```pulse
fn compute_dot_elem (p q: matrix_ref)
  (m n k : SZ.t)
  (i : SZ.t { SZ.v i < SZ.v m })
  (j : SZ.t { SZ.v j < SZ.v k })
  #pa #pb
  (#a: erased (matrix (SZ.v m) (SZ.v n)))
  (#b: erased (matrix (SZ.v n) (SZ.v k)))
  requires
    pts_to_matrix p #pa m n a **
    pts_to_matrix q #pb n k b
  returns y: r
  ensures
    pts_to_matrix p #pa m n a **
    pts_to_matrix q #pb n k b **
    pure (y == dot a b (SZ.v i) (SZ.v j))
{
  let mut l = 0sz;
  let mut acc = (0 <: r);
  while (let vl = !l; (vl `SZ.lt` n))
    invariant cond.
    pts_to_matrix p #pa m n a **
    pts_to_matrix q #pb n k b **
    (exists* vl vacc.
      R.pts_to l vl ** R.pts_to acc vacc
      ** pure (compute_dot_elem_inv i j a b vacc vl)
      ** pure (vl `SZ.lte` n)
      ** pure (cond == (vl `SZ.lt` n)))
  {
    let vl = !l;
    let vacc = !acc;
    let ail = matrix_idx p m n i vl;
    let blj = matrix_idx q n k vl j;
    acc := vacc + ail * blj;
    l := vl `SZ.add` 1sz;
  };
  !acc;
}
```

let matrix_eq_until #m #n (a b : matrix m n) (i: SZ.t) (j: SZ.t) : prop =
  SZ.v i <= m /\ SZ.v j <= n /\
  (forall (i' j' : nat). i' < SZ.v i /\ j' < n ==> a i' j' == b i' j') /\
  (SZ.v i < m ==> (forall (j': nat). j' < SZ.v j ==> a (SZ.v i) j' == b (SZ.v i) j'))

```pulse
fn matmul_serial_inner (p q res: matrix_ref)
  (m n k : SZ.t)
  #pa #pb
  (#a: erased (matrix (SZ.v m) (SZ.v n)))
  (#b: erased (matrix (SZ.v n) (SZ.v k)))
  (vi : SZ.t { SZ.v vi < SZ.v m })
  requires
    pts_to_matrix p #pa m n a **
    pts_to_matrix q #pb n k b **
    (exists* c.
      pts_to_matrix res m k c
      ** pure (matrix_eq_until c (dot a b) vi 0sz))
  returns _: unit
  ensures
    pts_to_matrix p #pa m n a **
    pts_to_matrix q #pb n k b **
    (exists* c.
      pts_to_matrix res m k c
      ** pure (matrix_eq_until c (dot a b) (vi `SZ.add` 1sz) 0sz))
{
  let mut j = 0sz;
  while (let vj = !j; (vj `SZ.lt` k))
    invariant cond.
    pts_to_matrix p #pa m n a **
    pts_to_matrix q #pb n k b **
    (exists* c vj.
      R.pts_to j vj ** pts_to_matrix res m k c
      ** pure (matrix_eq_until c (dot a b) vi vj)
      ** pure (cond == (vj `SZ.lt` k)))
  {
    let vj = !j;
    let y = compute_dot_elem p q m n k vi vj;
    matrix_upd res m k vi vj y;
    j := vj `SZ.add` 1sz;
  };
}
```

```pulse
fn matmul_serial (p q res: matrix_ref)
  (m n k : SZ.t)
  #pa #pb
  (#a: erased (matrix (SZ.v m) (SZ.v n)))
  (#b: erased (matrix (SZ.v n) (SZ.v k)))
  requires
    pts_to_matrix p #pa m n a **
    pts_to_matrix q #pb n k b **
    (exists* c. pts_to_matrix res m k c)
  returns _: unit
  ensures
    pts_to_matrix p #pa m n a **
    pts_to_matrix q #pb n k b **
    (exists* c. pts_to_matrix res m k c ** pure (c == dot a b))
{
  let mut i = 0sz;
  with c. assert pts_to_matrix res m k c;
  assert R.pts_to i 0sz;
  assert pts_to_matrix res m k c;
  while (let vi = !i; (vi `SZ.lt` m))
    invariant cond.
    pts_to_matrix p #pa m n a **
    pts_to_matrix q #pb n k b **
    (exists* c vi.
      R.pts_to i vi ** pts_to_matrix res m k c
      ** pure (matrix_eq_until c (dot a b) vi 0sz)
      ** pure (cond == (vi `SZ.lt` m)))
  {
    let vi = !i;
    matmul_serial_inner p q res m n k vi;
    i := vi `SZ.add` 1sz;
  };

  with c. assert pts_to_matrix res m k c;
  ext c (dot a b);
  assert pure (c == dot a b);
}
```