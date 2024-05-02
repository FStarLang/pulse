module Matmul.Matrix
open FStar.FunctionalExtensionality
open FStar.Mul

type r = int

type matrix (m n : nat) : Type0 =
  Fin.under m ^-> Fin.under n ^-> r

let mk #m #n (f : Fin.under m -> Fin.under n -> r) : matrix m n =
  on _ (fun i -> on _ (f i))

let zero #m #n : matrix m n =
  mk (fun i j -> 0)

let add #m #n (a b : matrix m n) : matrix m n =
  mk (fun i j -> a i j + b i j)

let ind (i j : nat) : r = if i = j then 1 else 0

let id #m : matrix m m = mk #m #m ind

let tr #m #n (a : matrix m n) : matrix n m = mk (fun i j -> a j i)

let smul #m #n (x : r) (a : matrix m n) : matrix m n =
  mk (fun i j -> x * a i j)

let ext #m #n (a b : matrix m n) : Lemma (requires forall i j. a i j == b i j) (ensures a == b) =
  introduce forall i. a i == b i with FunctionalExtensionality.extensionality _ _ (a i) (b i);
  FunctionalExtensionality.extensionality _ _ a b

let tr_tr #m #n (a : matrix m n) : Lemma (tr (tr a) == a) [SMTPat (tr (tr a))] =
  ext (tr (tr a)) a

let zero_tr m n : Lemma (tr (zero #m #n) == zero #n #m) [SMTPat (tr (zero #m #n))] =
  ext (tr (zero #m #n)) (zero #n #m)

let add_tr #m #n (a b : matrix m n) : Lemma (tr (add a b) == add (tr a) (tr b))
    [SMTPatOr [[SMTPat (tr (add a b))]; [SMTPat (add (tr a) (tr b))]]] =
  ext (tr (add a b)) (add (tr a) (tr b))

let id_tr m : Lemma (tr (id #m) == id #m) [SMTPat (tr (id #m))] =
  ext (tr (id #m)) id

let smul_tr #m #n (x : r) (a : matrix m n) : Lemma (tr (smul x a) == smul x (tr a))
    [SMTPatOr [[SMTPat (tr (smul x a))]; [SMTPat (smul x (tr a))]]] =
  ext (tr (smul x a)) (smul x (tr a))

let zero_add #m #n (a : matrix m n) : Lemma (add zero a == a) [SMTPat (add zero a)] =
  ext (add zero a) a

let add_zero #m #n (a : matrix m n) : Lemma (add a zero == a) [SMTPat (add a zero)] =
  ext (add a zero) a

let add_smul #m #n (x y : r) (a : matrix m n) : Lemma (smul (x + y) a == add (smul x a) (smul y a))
    [SMTPat (add (smul x a) (smul y a))] =
  ext (smul (x + y) a) (add (smul x a) (smul y a))

let smul_add #m #n (x : r) (a b : matrix m n) : Lemma (smul x (add a b) == add (smul x a) (smul x b))
    [SMTPatOr [[SMTPat (smul x (add a b))]; [SMTPat (add (smul x a) (smul x b))]]] =
  ext (smul x (add a b)) (add (smul x a) (smul x b))

let add_comm #m #n (a b : matrix  m n) : Lemma (add a b == add b a) = ext (add a b) (add b a)
let add_comm_pat () : squash (forall m n (a b : matrix m n). {:pattern add a b} add a b == add b a) =
  introduce forall m n (a b : matrix m n). add a b == add b a with add_comm a b

let add_assoc #m #n (a b c : matrix  m n) : Lemma (add a (add b c) == add (add a b) c) =
  ext (add a (add b c)) (add (add a b) c)
let add_assoc_pat : squash (forall m n (a b c : matrix  m n). {:pattern add a (add b c) \/ (add (add a b) c)} add a (add b c) == add (add a b) c) =
  introduce forall m n (a b c : matrix  m n). add a (add b c) == add (add a b) c with add_assoc a b c

let smul_zero #m #n (x : r) : Lemma (smul x zero == zero #m #n) [SMTPat (smul x (zero #m #n))] =
  ext (smul x zero) (zero #m #n)

let zero_smul #m #n (a : matrix m n) : Lemma (smul 0 a == zero #m #n) [SMTPat (smul 0 a)] =
  ext (smul 0 a) (zero #m #n)

let one_smul #m #n (a : matrix m n) : Lemma (smul 1 a == a) [SMTPat (smul 1 a)] =
  ext (smul 1 a) a

let smul_smul #m #n (x y : r) (a : matrix m n) : Lemma (smul x (smul y a) == smul (x * y) a) [SMTPat (smul x (smul y a))] =
  ext (smul x (smul y a)) (smul (x * y) a)

let rec bigsum (m : int) (n : int {m <= n}) (f : (int -> r)) : Tot r (decreases (n-m)) =
  if m = n then 0 else f (n-1) + bigsum m (n-1) f

let rec bigsum_congr (m:int) (n : int {m <= n}) (f g : int -> r)
  : Lemma (requires forall (i:int{m <= i /\ i < n}). f i == g i)
          (ensures bigsum m n f == bigsum m n g)
          (decreases n-m)
=
  if m = n then () else bigsum_congr m (n-1) f g

let shift (delta:int) (f:int -> 'a) : int -> 'a =
  fun x -> f (x + delta)

let rec bigsum_shift (m:int) (n : int {m <= n}) (f : int -> r)
        (delta : nat)
  : Lemma (ensures bigsum m n f == bigsum (m-delta) (n-delta) (shift delta f))
          (decreases n-m)
=
  if m = n then () else bigsum_shift m (n-1) f delta

let rec bigsum_split (m:int) (k:int{m <= k}) (n:int{k <= n}) (f : int -> r)
  : Lemma (ensures bigsum m n f == bigsum m k f + bigsum k n f)
          (decreases n-m)
  = if k = n then () else bigsum_split m k (n-1) f

let dot_summand #m #n #k (a : matrix m n) (b : matrix n k) i j (l : int) : r =
  if 0 <= l && l < n
  then a i l * b l j
  else 0
let dot #m #n #k (a : matrix m n) (b : matrix n k) : matrix m k =
  mk (fun i j -> bigsum 0 n (dot_summand a b i j))

let dot_tr #m #n #k (a : matrix m n) (b : matrix n k) :
    Lemma (tr (dot a b) == dot (tr b) (tr a))
      [SMTPatOr [[SMTPat (tr (dot a b))]; [SMTPat (dot (tr b) (tr a))]]] =
  introduce forall i j. tr (dot a b) i j == dot (tr b) (tr a) i j with
    bigsum_congr 0 n (dot_summand a b j i) (dot_summand (tr b) (tr a) i j);
  ext (tr (dot a b)) (dot (tr b) (tr a))

let dot_id #m #n (a : matrix m n) : Lemma (dot a id == a) [SMTPat (dot a id)] =
  introduce forall i j. dot a id i j == a i j with begin
    let rec aux (n':nat {n' <= n}) :
        Lemma (bigsum 0 n' (dot_summand a id i j) == (if j < n' then a i j else 0)) =
      if n' = 0 then () else aux (n'-1) in
    aux n
  end;
  ext (dot a id) a

let id_dot #m #n (a : matrix m n) : Lemma (dot id a == a) [SMTPat (dot id a)] =
  assert (tr (tr (dot id a)) == a)

let pointwise_add (f g : 'a -> r) : 'a -> r = fun x -> f x + g x
let pointwise_smul (k : r) (f : 'a -> r) : 'a -> r = fun x -> k * f x

let rec bigsum_pointwise_add
  (m : int) (n : int {m <= n})
  (f g : int -> r)
: Lemma (ensures bigsum m n (pointwise_add f g) == bigsum m n f + bigsum m n g)
        (decreases n-m)
= if m = n then () else bigsum_pointwise_add m (n-1) f g

let rec bigsum_smul
  (m : int) (n : int {m <= n})
  (k : r)
  (f : int -> r)
: Lemma (ensures bigsum m n (pointwise_smul k f) == k * bigsum m n f)
        (decreases n-m)
= if m = n then () else bigsum_smul m (n-1) k f

let dot_add #m #n #k (a : matrix m n) (b c : matrix n k) :
    Lemma (dot a (add b c) == add (dot a b) (dot a c))
      [SMTPatOr [[SMTPat (dot a (add b c))]; [SMTPat (add (dot a b) (dot a c))]]] =
  introduce forall i j. dot a (add b c) i j == add (dot a b) (dot a c) i j with begin
    calc (==) {
      dot a (add b c) i j;
      == {}
      bigsum 0 n (dot_summand a (add b c) i j);
      == { bigsum_congr 0 n (dot_summand a (add b c) i j)
                            (pointwise_add (dot_summand a b i j) (dot_summand a c i j)) }
      bigsum 0 n (pointwise_add (dot_summand a b i j) (dot_summand a c i j));
      == { bigsum_pointwise_add 0 n (dot_summand a b i j) (dot_summand a c i j) }
      bigsum 0 n (dot_summand a b i j) + bigsum 0 n (dot_summand a c i j);
      == {}
      add (dot a b) (dot a c) i j;
    }
  end;
  ext (dot a (add b c)) (add (dot a b) (dot a c))

let dot_smul #m #n #k (a : matrix m n) (x : r) (b : matrix n k) :
    Lemma (dot a (smul x b) == smul x (dot a b))
      [SMTPatOr [[SMTPat (dot a (smul x b))]; [SMTPat (smul x (dot a b))]]]
=
  introduce forall i j. dot a (smul x b) i j == smul x (dot a b) i j with
    calc (==) {
      dot a (smul x b) i j;
      == {}
      bigsum 0 n (dot_summand a (smul x b) i j);
      == { bigsum_congr 0 n (dot_summand a (smul x b) i j) (pointwise_smul x (dot_summand a b i j)) }
      bigsum 0 n (pointwise_smul x (dot_summand a b i j));
      == { bigsum_smul 0 n x (dot_summand a b i j) }
      x * bigsum 0 n (dot_summand a b i j);
      == {}
      smul x (dot a b) i j;
    };
  ext (dot a (smul x b)) (smul x (dot a b))

let add_dot #m #n #k (a b : matrix m n) (c : matrix n k) :
    Lemma (dot (add a b) c == add (dot a c) (dot b c))
      [SMTPatOr [[SMTPat (dot (add a b) c)]; [SMTPat (add (dot a c) (dot b c))]]] =
  assert (tr (tr (dot (add a b) c)) == add (dot a c) (dot b c))

let smul_dot #m #n #k (x : r) (a : matrix m n) (b : matrix n k) :
    Lemma (dot (smul x a) b == smul x (dot a b))
      [SMTPatOr [[SMTPat (dot (smul x a) b)]; [SMTPat (smul x (dot a b))]]] =
  assert (tr (tr (dot (smul x a) b)) == smul x (dot a b))

let sub #m #n (a : matrix m n)
    (k : nat) (m' : nat { k + m' <= m })
    (l : nat) (n' : nat { l + n' <= n }) :
    matrix m' n' =
  mk #m' #n' (fun i j -> a (k+i) (l+j))

let hsub #m #n (a : matrix m n) (l : nat) (n' : nat { l + n' <= n }) : matrix m n' =
  sub a 0 m l n'

let vsub #m #n (a : matrix m n) (k : nat) (m' : nat { k + m' <= m }) : matrix m' n =
  sub a k m' 0 n

let hcat #m #n #k (a : matrix m n) (b : matrix m k) (n' : nat {n' == n+k}) : matrix m n' =
  mk #m #n' (fun i j -> if j < n then a i j else b i (j-n))

let vcat #m #n #k (a : matrix m n) (b : matrix k n) (m' : nat {m' == m+k}) : matrix m' n =
  mk #m' #n (fun i j -> if i < m then a i j else b (i-m) j)

let hsplit1 #m #n (a : matrix m n) (i : nat { i <= n }) = hsub a 0 i
let hsplit2 #m #n (a : matrix m n) (i : nat { i <= n }) = hsub a i (n-i)
let hsplit #m #n (a : matrix m n) (i : nat { i <= n }) = (hsplit1 a i, hsplit2 a i)

let vsplit1 #m #n (a : matrix m n) (j : nat { j <= m }) = vsub a 0 j
let vsplit2 #m #n (a : matrix m n) (j : nat { j <= m }) = vsub a j (m-j)
let vsplit #m #n (a : matrix m n) (j : nat { j <= m }) = (vsplit1 a j, vsplit2 a j)

let hcat_hsplit #m #n (a : matrix m n) (i : nat { i <= n }) :
    Lemma (let (a1, a2) = hsplit a i in hcat a1 a2 n == a) =
  let (a1, a2) = hsplit a i in ext (hcat a1 a2 n) a

let vcat_vsplit #m #n (a : matrix m n) (j : nat { j <= m }) :
    Lemma (let (a1, a2) = vsplit a j in vcat a1 a2 m == a) =
  let (a1, a2) = vsplit a j in ext (vcat a1 a2 m) a

let hcat_tr #m #n #k (a : matrix m n) (b : matrix m k) (n' : nat {n' == n+k}) :
    Lemma (tr (hcat a b n') == vcat (tr a) (tr b) n')
      [SMTPatOr [[SMTPat (tr (hcat a b n'))]; [SMTPat (vcat (tr a) (tr b) n')]]] =
  ext (tr (hcat a b n')) (vcat (tr a) (tr b) n')

let vcat_tr #m #n #k (a : matrix m n) (b : matrix k n) (m' : nat {m' == m+k}) :
    Lemma (tr (vcat a b m') == hcat (tr a) (tr b) m')
      [SMTPatOr [[SMTPat (tr (vcat a b m'))]; [SMTPat (hcat (tr a) (tr b) m')]]] =
  ext (tr (vcat a b m')) (hcat (tr a) (tr b) m')

let dot_hcat #m #n #k #l (a : matrix m n) (b : matrix n k) (c : matrix n l) (k' : nat {k' == k+l}) :
    Lemma (dot a (hcat b c k') == hcat (dot a b) (dot a c) k') =
  introduce forall i j. dot a (hcat b c k') i j == hcat (dot a b) (dot a c) k' i j with
    bigsum_congr 0 n (dot_summand a (hcat b c k') i j) (if j < k then dot_summand a b i j else dot_summand a c i (j-k));
  ext (dot a (hcat b c k')) (hcat (dot a b) (dot a c) k')

let vcat_dot #m1 #m2 #n #k (a1 : matrix m1 n) (a2 : matrix m2 n) (b : matrix n k) (m : nat {m == m1+m2}) :
    Lemma (dot (vcat a1 a2 m) b == vcat (dot a1 b) (dot a2 b) m) =
  dot_hcat (tr b) (tr a1) (tr a2) m;
  assert (tr (tr (dot (vcat a1 a2 m) b)) == vcat (dot a1 b) (dot a2 b) m)

(*
         B1
         B2
  A1 A2  C     ==> C = A1B1 + A2B2
*)
let hcat_dot_vcat #m #n1 #n2 #k (a1 : matrix m n1) (a2 : matrix m n2) (b1 : matrix n1 k) (b2 : matrix n2 k) (n : nat {n==n1+n2}) :
    Lemma (dot (hcat a1 a2 n) (vcat b1 b2 n) == add (dot a1 b1) (dot a2 b2)) =
  introduce forall i j. dot (hcat a1 a2 n) (vcat b1 b2 n) i j == add (dot a1 b1) (dot a2 b2) i j with begin
    calc (==) {
      dot (hcat a1 a2 n) (vcat b1 b2 n) i j;
      == {}
      bigsum 0 n (dot_summand (hcat a1 a2 n) (vcat b1 b2 n) i j);
      == { bigsum_split 0 n1 n (dot_summand (hcat a1 a2 n) (vcat b1 b2 n) i j) }
        bigsum 0 n1 (dot_summand (hcat a1 a2 n) (vcat b1 b2 n) i j)
      + bigsum n1 n (dot_summand (hcat a1 a2 n) (vcat b1 b2 n) i j);
      == { bigsum_congr 0 n1 (dot_summand (hcat a1 a2 n) (vcat b1 b2 n) i j) (dot_summand a1 b1 i j) }
        bigsum 0 n1 (dot_summand a1 b1 i j)
      + bigsum n1 n (dot_summand (hcat a1 a2 n) (vcat b1 b2 n) i j);
      == { bigsum_shift n1 n (dot_summand (hcat a1 a2 n) (vcat b1 b2 n) i j) n1 }
        bigsum 0 n1 (dot_summand a1 b1 i j)
      + bigsum 0 n2 (shift n1 (dot_summand (hcat a1 a2 n) (vcat b1 b2 n) i j));
      == { bigsum_congr 0 n2 (shift n1 (dot_summand (hcat a1 a2 n) (vcat b1 b2 n) i j))
                             (dot_summand a2 b2 i j) }
        bigsum 0 n1 (dot_summand a1 b1 i j)
      + bigsum 0 n2 (dot_summand a2 b2 i j);
      == { () }
      add (dot a1 b1) (dot a2 b2) i j;
    }
  end;
  ext (dot (hcat a1 a2 n) (vcat b1 b2 n)) (add (dot a1 b1) (dot a2 b2))
