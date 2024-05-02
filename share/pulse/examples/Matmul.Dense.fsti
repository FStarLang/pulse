module Matmul.Dense
open Matmul.Matrix
open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.Tactics.V2
open FStar.Mul
open FStar.FunctionalExtensionality
module SZ = FStar.SizeT

let pts_to_elem #t (a:array t)
    ([@@@ equate_by_smt] i:erased nat)
    (#[exact (`1.0R)] p:perm)
    ([@@@ equate_by_smt] x: t) : vprop =
  pts_to_range a i (i + 1) #p (Seq.create 1 x)

```pulse
ghost fn pts_to_elem_prop #t (a:array t) i (#p:perm) (x: erased t)
  requires pts_to_elem a i #p x
  returns _: unit
  ensures pure (i < length a) ** pts_to_elem a i #p x
{
  unfold pts_to_elem a i #p x;
  pts_to_range_prop a;
  fold pts_to_elem a i #p x;
}
```

```pulse
fn pts_to_elem_idx #t (a:array t) #i' (i:SZ.t { SZ.v i == i' }) (#p:perm) (#x: erased t)
  requires pts_to_elem a i' #p x
  returns y:t
  ensures pure (y == x) ** pts_to_elem a i' #p x
{
  unfold pts_to_elem a (SZ.v i) #p x;
  let y = pts_to_range_index a i;
  fold pts_to_elem a (SZ.v i) #p x;
  y;
}
```

```pulse
fn pts_to_elem_upd #t (a:array t) (i:SZ.t) (#x: erased t) (y: t)
  requires pts_to_elem a (SZ.v i) x
  returns _:unit
  ensures pts_to_elem a (SZ.v i) y
{
  unfold pts_to_elem a (SZ.v i) x;
  pts_to_range_upd a i y;
  with s. assert (pts_to_range a (SZ.v i) (SZ.v i + 1) s);
  assert pure (Seq.equal (Seq.create 1 y) s);
  fold pts_to_elem a (SZ.v i) y;
}
```

let rec bigstar (m : nat) (n : nat {m <= n}) (f : (i:nat { m <= i /\ i < n } -> vprop)) : Tot vprop (decreases n - m) =
  if m = n then emp else f m ** bigstar (m+1) n f

let star_aci () :
    squash (
      (forall (a b : vprop). {:pattern (a ** b)} a ** b == b ** a) /\
      (forall (a : vprop). {:pattern (a ** emp)} a ** emp == a) /\
      (forall (a b c : vprop). {:pattern (a ** b ** c)} a ** (b ** c) == (a ** b) ** c)) =
  introduce forall (a b : vprop). a ** b == b ** a with elim_vprop_equiv (vprop_equiv_comm a b);
  introduce forall (a : vprop). a ** emp == a with elim_vprop_equiv (vprop_equiv_unit a);
  introduce forall (a b c : vprop). a ** (b ** c) == (a ** b) ** c with elim_vprop_equiv (vprop_equiv_assoc a b c)

let rec bigstar_split (m : nat) (n : nat {m <= n}) f (i : nat { m <= i /\ i <= n }) :
    Lemma (ensures bigstar m n f == bigstar m i f ** bigstar i n f) (decreases n - m) =
  star_aci ();
  if m = i then () else bigstar_split (m+1) n f i

let rec bigstar_star (m : nat) (n : nat {m <= n}) f g h
    (heq : (i:nat { m <= i /\ i < n }) -> squash (f i ** g i == h i)) :
    Pure
      (squash (bigstar m n f ** bigstar m n g == bigstar m n h))
      (requires True) //forall i. f i ** g i == h i)
      (ensures fun _ -> True)
      (decreases n - m) =
  star_aci ();
  if m = n then () else (bigstar_star (m+1) n f g h heq; heq m)

let rec bigstar_congr (m : nat) (n : nat { m <= n }) (m' : nat) (n' : nat { m' <= n' /\ n' - m' == n - m })
    (f : (i:nat { m <= i /\ i < n }) -> vprop) (f' : (i:nat { m' <= i /\ i < n' }) -> vprop) 
    (h : ((i:nat{i < n-m}) -> squash (f (m+i) == f' (m'+i))))
    :
    Pure
      (squash (bigstar m n f == bigstar m' n' f'))
      (requires True)
      (ensures fun _ -> True)
      (decreases n-m)
       =
  if m = n then () else begin
    bigstar_congr (m+1) n (m'+1) n' f f' (fun i -> h (i+1));
    h 0
  end

type matrix_ref = array r

let pts_to_vec_fun (p: matrix_ref) (#n: nat) (off : nat) (pr:perm) (a: (Fin.under n ^-> r)) j : vprop =
  pts_to_elem p (off + j) #pr (a j)
let pts_to_vec (p: matrix_ref) (#n: nat) (off : nat) (#[exact (`1.0R)] pr:perm) (a: (Fin.under n ^-> r)) : vprop =
  bigstar 0 n (pts_to_vec_fun p off pr a)

let pts_to_matrix_fun (p: matrix_ref) (#m: nat) (#n: nat) (off : nat) (stride: nat) (pr:perm) (a: (matrix m n)) (i:nat { i < m }) : vprop =
  pts_to_vec p (off + stride*i) #pr (a i)
let pts_to_matrix (p: matrix_ref) (#m: nat) (#n: nat) (off : nat) (stride: nat) (#[exact (`1.0R)] pr:perm) (a: (matrix m n)) : vprop =
  bigstar 0 m (pts_to_matrix_fun p off stride pr a)

#push-options "--split_queries always"
let pts_to_matrix_vsplit (p: matrix_ref) #m #n (i: nat { i <= m }) o s pr (a : matrix m n) :
    Lemma (pts_to_matrix p o s #pr a ==
      (let (a1, a2) = vsplit a i in pts_to_matrix p o s #pr a1 ** pts_to_matrix p (o+s*i) s #pr a2)) =
  bigstar_split 0 m (pts_to_matrix_fun p o s pr a) i;
  let (a1, a2) = vsplit a i in
  let _ : squash (bigstar 0 i (pts_to_matrix_fun p o s pr a) == pts_to_matrix p o s #pr a1) =
    bigstar_congr 0 i 0 i (pts_to_matrix_fun p o s pr a) (pts_to_matrix_fun p o s pr a1) (fun i ->
      bigstar_congr _ _ _ _ _ _ (fun j -> ())) in
  let _ : squash (bigstar i m (pts_to_matrix_fun p o s pr a) == pts_to_matrix p (o+s*i) s #pr a2) =
    bigstar_congr _ _ _ _ _ _ (fun k ->
      Math.Lemmas.distributivity_add_left i k s;
      Math.Lemmas.lemma_mult_le_left s 0 (i+k);
      bigstar_congr 0 n 0 n (pts_to_vec_fun p (o + s*(i+k) <: nat) pr (a (i+k))) (pts_to_vec_fun p ((o + s*i) + s*(0+k) <: nat) pr (a2 k)) (fun j ->
        assert ((i+k) * s == i*s + k*s);
        assert (s * (i+k) + j == s * i + s * k + j);
        assert (a (i+k) j == a2 k j);
        assert (pts_to_vec_fun p (o + s * (i + k)) pr (a (i + k)) (0 + j) == pts_to_vec_fun p (o + s * i + s * (0 + k)) pr (a2 k) (0 + j));
        ())) in
  ()
#pop-options

let show_using t (x:t) : t = x

let pts_to_matrix_hsplit (p: matrix_ref) #m #n (i: nat { i <= n }) o s pr (a : (matrix m n)) :
    Lemma (pts_to_matrix p o s #pr a ==
      (let (a1, a2) = hsplit a i in pts_to_matrix p o s #pr a1 ** pts_to_matrix p (o+i) s #pr a2)) =
  let (a1, a2) = hsplit a i in
  squash (pts_to_matrix p o s #pr a1 ** pts_to_matrix p (o+i) s #pr a2 == pts_to_matrix p o s #pr a) `show_using`
  bigstar_star _ _ _ _ _ (fun k ->
    squash (pts_to_matrix_fun p o s pr a1 k ** pts_to_matrix_fun p (o + i) s pr a2 k == pts_to_matrix_fun p o s pr a k) `show_using` begin
    Math.Lemmas.lemma_mult_le_left s 0 k;

    bigstar_split 0 n (pts_to_vec_fun p (o+s*k) pr (a k)) i;
    assert (pts_to_matrix_fun p o s pr a k ==
      (bigstar 0 i (pts_to_vec_fun p (o+s*k) pr (a k))) **
      (bigstar i n (pts_to_vec_fun p (o+s*k) pr (a k))));

    assert_norm (pts_to_matrix_fun p o s pr a1 k == bigstar 0 i (pts_to_vec_fun p (o+s*k) pr (a1 k)));
    squash (pts_to_matrix_fun p o s pr a1 k == bigstar 0 i (pts_to_vec_fun p (o+s*k) pr (a k))) `show_using`
      bigstar_congr _ _ _ _ _ _ (fun j -> magic ());
    
    squash (pts_to_matrix_fun p (o+i) s pr a2 k == bigstar i n (pts_to_vec_fun p (o+s*k) pr (a k))) `show_using`
      bigstar_congr _ _ _ _ _ _ (fun j -> magic ());

    () end)

let matrix_of_seq (m n : nat) (s: Seq.seq r { Seq.length s == m*n }) : matrix m n =
  mk (fun i j ->
    assert (n*i <= n*(m-1));
    Seq.index s (n*i + j))

```pulse
ghost fn rw (a b : vprop) requires a ** pure (a == b) ensures b {
  rewrite a as b
}
```

```pulse
ghost fn pts_to_matrix_hsplit' (p : matrix_ref) #m #n (i : nat { i <= n}) (o s : nat) (pr: perm) (a : matrix m n)
  requires pts_to_matrix p o s #pr a
  returns _: unit
  ensures
      pts_to_matrix p o s #pr (hsplit1 a i) **
      pts_to_matrix p (o+i) s #pr (hsplit2 a i)
{
  pts_to_matrix_hsplit p i o s pr a;
  rw (pts_to_matrix p o s #pr a)
    (pts_to_matrix p o s #pr (hsplit a i)._1 **
      pts_to_matrix p (o+i) s #pr (hsplit a i)._2);
}
```

```pulse
ghost fn bigstar_extract
    (m : nat)
    (n : nat {m <= n})
    (f: (i: nat{m <= i /\ i < n} -> vprop))
    (i : nat { m <= i /\ i < n })
  requires bigstar m n f
  returns _:unit
  ensures bigstar m i f ** f i ** bigstar (i+1) n f
{
  bigstar_split m n f i;
  rw (bigstar m n f) (bigstar m i f ** bigstar i n f);
  rw (bigstar i n f) (f i ** bigstar (i+1) n f);
}
```

```pulse
ghost fn bigstar_compose
    (m : nat)
    (n : nat {m <= n})
    (f: (i: nat{m <= i /\ i < n} -> vprop))
    (i : nat { m <= i /\ i < n })
  requires bigstar m i f ** f i ** bigstar (i+1) n f
  returns _:unit
  ensures bigstar m n f
{
  bigstar_split m n f i;
  rw (f i ** bigstar (i+1) n f) (bigstar i n f);
  rw (bigstar m i f ** bigstar i n f) (bigstar m n f);
}
```

```pulse
ghost fn pts_to_matrix_vsplit' (p : matrix_ref) #m #n (i : nat { i <= m }) (o s : nat) (pr: perm) (a : matrix m n)
  requires pts_to_matrix p o s #pr a
  returns _: unit
  ensures
      pts_to_matrix p o s #pr (vsplit1 a i) **
      pts_to_matrix p (o+s*i) s #pr (vsplit2 a i)
{
  pts_to_matrix_vsplit p i o s pr a;
  rw (pts_to_matrix p o s #pr a)
    (pts_to_matrix p o s #pr (vsplit a i)._1 **
      pts_to_matrix p (o+s*i) s #pr (vsplit a i)._2);
}
```

```pulse
ghost fn unfold_pts_to_matrix
  (p: matrix_ref) (#m: nat) (#n: nat) (off : nat) (stride: nat) (pr:perm) (a: (matrix m n))
  requires pts_to_matrix p off stride #pr a
  returns _:unit
  ensures bigstar 0 m (pts_to_matrix_fun p off stride pr a)
{
  rw (pts_to_matrix p off stride #pr a) (bigstar 0 m (pts_to_matrix_fun p off stride pr a));
}
```

```pulse
fn matrix_idx (p: matrix_ref) (#m: erased nat) (#n: erased nat) (off : SZ.t) (stride: SZ.t) #pr
    (i : SZ.t { SZ.v i < m })
    (j : SZ.t { SZ.v j < n })
    (a: erased (matrix m n))
  requires pts_to_matrix p (SZ.v off) (SZ.v stride) #pr a
  returns x:r
  ensures pure (x == reveal a (SZ.v i) (SZ.v j)) **
  pts_to_matrix p (SZ.v off) (SZ.v stride) #pr a
{
  unfold_pts_to_matrix p #m #n (SZ.v off) (SZ.v stride) pr a;
  bigstar_extract 0 m (pts_to_matrix_fun p (SZ.v off) (SZ.v stride) pr a) (SZ.v i);
  rw (pts_to_matrix_fun p (SZ.v off) (SZ.v stride) pr (reveal a) (SZ.v i)) (bigstar 0 n (pts_to_vec_fun p (SZ.v off + SZ.v stride * SZ.v i) pr (reveal a (SZ.v i))));
  bigstar_extract 0 n _ (SZ.v j);
  rw (pts_to_vec_fun p (SZ.v off + SZ.v stride * SZ.v i) pr (reveal a (SZ.v i)) (SZ.v j))
    (pts_to_elem p (SZ.v off + SZ.v stride * SZ.v i + SZ.v j) #pr (reveal a (SZ.v i) (SZ.v j)));
  pts_to_elem_prop p (SZ.v off + SZ.v stride * SZ.v i + SZ.v j) #pr (reveal a (SZ.v i) (SZ.v j));
  let x = pts_to_elem_idx p #(SZ.v off + SZ.v stride * SZ.v i + SZ.v j) (off `SZ.add` (stride `SZ.mul` i) `SZ.add` j) #pr #(reveal a (SZ.v i) (SZ.v j));
  rw (pts_to_elem p (SZ.v off + SZ.v stride * SZ.v i + SZ.v j) #pr (reveal a (SZ.v i) (SZ.v j)))
    (pts_to_vec_fun p (SZ.v off + SZ.v stride * SZ.v i) pr (reveal a (SZ.v i)) (SZ.v j));
  bigstar_compose 0 n (pts_to_vec_fun p (SZ.v off + SZ.v stride * SZ.v i) pr (reveal a (SZ.v i))) (SZ.v j);
  rw (bigstar 0 n (pts_to_vec_fun p (SZ.v off + SZ.v stride * SZ.v i) pr (reveal a (SZ.v i))))
    (pts_to_matrix_fun p (SZ.v off) (SZ.v stride) pr (reveal a) (SZ.v i));
  bigstar_compose 0 m _ (SZ.v i);
  fold pts_to_matrix p (SZ.v off) (SZ.v stride) #pr a;
  x;
}
```

```pulse
fn matmul_serial (a b c : matrix_ref) (oa sa ob sb oc sc : SZ.t) (#pa #pb : perm)
    (#m #n #k : erased nat) (a' : erased (matrix m n)) (b' : erased (matrix n k))
  requires
    pts_to_matrix a (SZ.v oa) (SZ.v sa) #pa a' **
    pts_to_matrix b (SZ.v ob) (SZ.v sb) #pb b' **
    (exists* (buf : matrix m k). pts_to_matrix c (SZ.v oc) (SZ.v sc) buf)
  returns _:unit
  ensures
    pts_to_matrix a (SZ.v oa) (SZ.v sa) #pa a' **
    pts_to_matrix b (SZ.v ob) (SZ.v sb) #pb b' **
    pts_to_matrix c (SZ.v oc) (SZ.v sc) (dot a' b')
{
  let mut i = 0sz;
  while (let vi = !i; (vi `SZ.lt` m))
    invariant cond.
      exists* vi. Pulse.Lib.Reference.pts_to i vi **
      // pts_to_matrix a (SZ.v oa) (SZ.v sa) #pa a' **
      // pts_to_matrix b (SZ.v ob) (SZ.v sb) #pb b' **
      // (exists* (buf : matrix m k). pts_to_matrix c (SZ.v oc) (SZ.v sc) buf) **
      emp
  {
    admit();
  }
}
```
