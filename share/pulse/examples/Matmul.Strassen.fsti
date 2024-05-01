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

// val seq_mk #a (n:nat) (f: Fin.under n -> a) : Seq.seq a
// val seq_mk_length #a n (f: Fin.under n -> a) : Lemma (Seq.length (seq_mk n f) == n) [SMTPat (Seq.length (seq_mk n f))]
// val seq_mk_nth #a n (f: Fin.under n -> a) (i: Fin.under n) : Lemma (Seq.index (seq_mk n f) i == f i) [SMTPat (Seq.index (seq_mk n f) i)]

let upd #m #n (a : matrix m n) (i : Fin.under m) (j : Fin.under n) (x : r) : matrix m n =
  mk (fun i' j' -> if i = i' && j = j' then x else a i' j')

let of_col_maj (m n : nat) (s: Seq.seq r { Seq.length s == m*n }) : matrix m n =
  mk (fun i j ->
    assert (n*i <= n*(m-1));
    Seq.index s (n*i + j))

let pts_to_matrix (p: matrix_ref) (#[exact (`full_perm)] pr:perm) (m: SZ.t) (n: SZ.t) (a: matrix (SZ.v m) (SZ.v n)) : vprop =
  exists* (buf : Seq.seq r).
    pts_to p buf ** pure (Seq.length buf == SZ.v m * SZ.v n /\ of_col_maj (SZ.v m) (SZ.v n) buf == a)

```pulse
fn matrix_idx (p: matrix_ref) (m : SZ.t) (n : SZ.t) (i : SZ.t { SZ.v i < SZ.v m }) (j : SZ.t { SZ.v j < SZ.v n }) (#a: erased (matrix (SZ.v m) (SZ.v n)))
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

// let col_maj_idx_inj () :
//   squash (forall (n i1 j1 i2 j2 : nat).
//     {:pattern (n*i1 + j1 == n*i2 + j2)}
//     j1 < n /\ j2 < n /\
//     n*i1 + j1 == n*i2 + j2 ==> i1 == i2 /\ j1 == j2) = admit ()

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

```pulse
fn matmul_serial (p q res: matrix_ref)
  (m n k : SZ.t)
  (i : SZ.t { SZ.v i < SZ.v m })
  (j : SZ.t { SZ.v j < SZ.v k })
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
    pts_to_matrix res m k (dot a b)
{
  let mut i = 0sz;
  while (let vi = !i; (vi `SZ.lt` m))
    invariant cond.
    pts_to_matrix p #pa m n a **
    pts_to_matrix q #pb n k b **
    (exists* c vi.
      R.pts_to i vi ** pts_to_matrix res m k c
      ** pure (SZ.v vi <= SZ.v m /\ cond == (vi `SZ.lt` m))
      ** pure (forall (i' : Fin.under (SZ.v m)) (j' : Fin.under (SZ.v n)).
        i' < SZ.v vi /\ j' < SZ.v n ==> c i' j' == dot a b i' j'))
  {
    let vi = !i;
    let mut j = 0sz;
    while (let vj = !j; (vj `SZ.lt` n))
      invariant cond.
      pts_to_matrix p #pa m n a **
      pts_to_matrix q #pb n k b **
      (exists* c vj.
        R.pts_to j vj ** pts_to_matrix res m k c
        ** pure (forall (i' j' : nat). i' < SZ.v vi /\ j' < SZ.v n ==> c i' j' == dot a b i' j')
        ** pure (SZ.v vj <= SZ.v n /\ cond == (vj `SZ.lt` n) /\
          (forall (j': nat). j' < SZ.v vj ==> c (SZ.v vi) j' == dot a b (SZ.v vi) j')))
    {
      let vj = !j;
      let y = compute_dot_elem p q m n k vi vj;
      matrix_upd res m k vi vj y;
      j := vj `SZ.add` 1sz;
    };

    i := vi `SZ.add` 1sz;
    admit ();
  };
  with c. assert pts_to_matrix res m k c;
  ext c (dot a b);
}
```