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
  ();
  pts_to_len p;
  assert pure (SZ.v n * SZ.v i + SZ.v j < SZ.v n * (SZ.v i + 1));
  let x = p.((n `SZ.mul` i) `SZ.add` j);
  ();
  fold pts_to_matrix p #pr m n a;
  x;
}
```

```pulse
fn matrix_upd (p: matrix_ref) (m : SZ.t) (n : SZ.t) (i : SZ.t { SZ.v i < SZ.v m }) (j : SZ.t { SZ.v j < SZ.v n }) (#a: erased (matrix (SZ.v m) (SZ.v n))) (y: r)
  requires pts_to_matrix p m n a
  returns _: unit
  ensures pts_to_matrix p m n (upd a (SZ.v i) (SZ.v j) y)
{
  unfold pts_to_matrix p m n a;
  ();
  pts_to_len p;
  assert pure (SZ.v n * SZ.v i + SZ.v j < SZ.v n * (SZ.v i + 1));
  p.((n `SZ.mul` i) `SZ.add` j) <- y;
  with buf. assert pts_to p buf;
  ();
  magic #(of_col_maj _ _ buf == upd a (SZ.v i) (SZ.v j) y) (); // TODO
  fold pts_to_matrix p m n (upd a (SZ.v i) (SZ.v j) y);
  ();
}
```

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
  admit ();
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