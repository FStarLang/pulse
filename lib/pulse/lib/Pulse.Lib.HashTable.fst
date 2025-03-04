(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Pulse.Lib.HashTable
#lang-pulse
open Pulse.Lib.Pervasives
module V = Pulse.Lib.Vec
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module PHT = Pulse.Lib.HashTable.Spec

open Pulse.Lib.HashTable.Spec
open Pulse.Lib.HashTable.Type

let mk_used_cell
  (#[@@@ Rust_generics_bounds ["Copy"; "PartialEq"; "Clone"]] a:eqtype)
  (#[@@@ Rust_generics_bounds ["Clone"]] b:Type)
  (k:a) (v:b) : cell a b =

  Used k v

let mk_ht
  (#[@@@ Rust_generics_bounds ["Copy"; "PartialEq"; "Clone"]] k:eqtype)
  (#[@@@ Rust_generics_bounds ["Clone"]] v:Type)
  (sz:pos_us)
  (hashf:k -> SZ.t)
  (contents:V.vec (cell k v))
  : ht_t k v
  = { sz; hashf; contents; }

let models_timeless #kt #vt (ht:ht_t kt vt) (pht:pht_t kt vt)
  : Lemma (timeless (models ht pht))
          [SMTPat (timeless (models ht pht))] = ()

(* NOTE: We do not add the Rust attributes in these definitions since
   1- They anyway be ignored by Pulse (currently, should fix)
   2- The ones that really matter are the ones in the declarations
      in the fsti (which currently are, and must be, F* vals).
*)

fn alloc
  (#k:eqtype)
  (#v:Type0)
  (hashf:(k -> SZ.t)) (l:pos_us)
  requires pure (SZ.fits (2 `op_Multiply` SZ.v l))
  returns ht:ht_t k v
  ensures exists* pht. models ht pht ** pure (pht == mk_init_pht hashf l)
{
  let contents = V.alloc #(cell k v) Clean l;
  let ht = mk_ht l hashf contents;
  let pht = Ghost.hide (mk_init_pht #k #v hashf l);
  rewrite (V.pts_to contents (Seq.create (SZ.v l) Clean))
       as (V.pts_to ht.contents pht.repr.seq);
  fold models;
  ht
}

fn dealloc
  (#k:eqtype)
  (#v:Type0)
  (ht:ht_t k v)
  requires exists* pht. models ht pht
  ensures emp
{
  open SZ;
  unfold models;
  V.free ht.contents;
}


let size_t_mod (x:SZ.t) (y : SZ.t { y =!= 0sz })
: z:SZ.t { SZ.v z == SZ.v x % SZ.v y }
  = SZ.(x %^ y)

#push-options "--fuel 1 --ifuel 1"

fn lookup
  (#kt:eqtype)
  (#vt:Type0)
  (#pht:erased (pht_t kt vt))
  (ht:ht_t kt vt)
  (k:kt)
  requires models ht pht
  returns  p:(ht_t kt vt & option SZ.t)
  ensures  models (fst p) pht **
           pure (same_sz_and_hashf (fst p) ht /\ (snd p == PHT.lookup_index_us pht k))
{
  open SZ;

  let hashf = ht.hashf;
  let mut contents = ht.contents;

  let cidx = size_t_mod (hashf k) ht.sz;
  let mut off = 0sz;
  let mut cont = true;
  let mut ret = None #SZ.t;
  unfold (models ht pht);

  while (let voff = !off;
         let vcont = !cont;
         (voff <=^ ht.sz && vcont = true))
  invariant b. exists* (voff:SZ.t) (vcont :bool) vcontents. (
    pts_to contents vcontents **
    V.pts_to vcontents pht.repr.seq **
    pts_to off voff **
    pts_to cont vcont **
    pts_to ret (if vcont then None else (PHT.lookup_index_us pht k)) **
    pure (
      SZ.v ht.sz == pht_sz pht /\
      V.is_full_vec vcontents /\
      voff <=^ ht.sz /\
      walk_get_idx pht.repr (SZ.v cidx) k (SZ.v voff)
        == lookup_repr_index pht.repr k /\
      b == (voff <=^ ht.sz && vcont = true)
    ))
  {
    let voff = !off;
    if (voff = ht.sz)
    {
      cont := false;
      assert (pts_to ret None);
    }
    else
    {
      let sum = cidx +^ voff;
      let idx = size_t_mod sum ht.sz;
      let c = V.replace_i_ref contents idx Zombie;
      match c
      {
        Used k' v' ->
        {
          if (k' = k)
          {
            cont := false;
            ret := Some idx;
            let _ = V.replace_i_ref contents idx (Used k' v');
            with vcontents. assert (pts_to contents vcontents);
            with s. assert (pts_to vcontents s);
            assert (pure (Seq.equal s pht.repr.seq));
            assert (pure (pht.repr @@ SZ.v idx == Used k' v'));
            assert (pure (lookup_repr_index pht.repr k == Some (v', SZ.v idx)));
          } else
          {
            off := voff +^ 1sz;
            let _ = V.replace_i_ref contents idx (Used k' v');
            with vcontents. assert (pts_to contents vcontents);
            with s. assert (pts_to vcontents s);
            assert (pure (Seq.equal s pht.repr.seq));
            assert (pure (walk_get_idx pht.repr (SZ.v cidx) k (SZ.v voff)
              == walk_get_idx pht.repr (SZ.v cidx) k (SZ.v (voff+^1sz))));
          }
        }
        Clean ->
        {
          cont := false;
          let _ = V.replace_i_ref contents idx c;
          with vcontents. assert (pts_to contents vcontents);
          with s. assert (pts_to vcontents s);
          assert (pure (Seq.equal s pht.repr.seq));
          assert (pure (walk_get_idx pht.repr (SZ.v cidx) k (SZ.v voff) == None));
          assert (pts_to ret (PHT.lookup_index_us pht k));
        }
        Zombie ->
        {
          off := voff +^ 1sz;
          let _ = V.replace_i_ref contents idx c;
          with vcontents. assert (pts_to contents vcontents);
          with s. assert (pts_to vcontents s);
          assert (pure (Seq.equal s pht.repr.seq));
          assert (pure (walk_get_idx pht.repr (SZ.v cidx) k (SZ.v voff)
            == walk_get_idx pht.repr (SZ.v cidx) k (SZ.v (voff+^1sz))));
        }
      }
    }
  };
  let o = !ret;

  let vcontents = !contents;
  let ht = mk_ht ht.sz ht.hashf vcontents;
  with vcontents_g. assert (pts_to contents vcontents_g);
  rewrite (V.pts_to vcontents_g pht.repr.seq) as (V.pts_to ht.contents pht.repr.seq);
  fold (models ht pht);
  let res = ((ht <: ht_t kt vt), o);
  assert (pts_to ret (PHT.lookup_index_us pht k));
  rewrite (models ht pht) as (models (fst res) pht);
  res
}

#pop-options


fn replace
  (#kt:eqtype)
  (#vt:Type0)
  (#pht:erased (pht_t kt vt))
  (ht:ht_t kt vt)
  (idx:SZ.t)
  (k:kt)
  (v:vt)
  (_:squash (SZ.v idx < Seq.length pht.repr.seq /\ PHT.lookup_index_us pht k == Some idx))

  requires models ht pht
  returns p:(ht_t kt vt & vt)
  ensures models (fst p) (PHT.upd_pht #kt #vt pht idx k v ()) **
          pure (same_sz_and_hashf (fst p) ht /\ Some (snd p) == PHT.lookup pht k)
{
  let hashf = ht.hashf;
  let mut contents = ht.contents;
  unfold models;
  rewrite (pts_to contents ht.contents) as (pts_to contents (reveal (hide ht.contents)));
  rewrite (V.pts_to ht.contents pht.repr.seq) as (V.pts_to (reveal (hide ht.contents)) pht.repr.seq);
  let v' = V.replace_i_ref contents idx (mk_used_cell k v);
  let vcontents = !contents;
  let ht1 = mk_ht ht.sz hashf vcontents;
  with s. rewrite (V.pts_to (reveal (hide ht.contents)) s) as (V.pts_to ht1.contents s);
  fold (models ht1 (PHT.upd_pht pht idx k v ()));
  match v' {
    Used k' v' -> {
      let res = ((ht1 <: ht_t kt vt), v');
      with pht. rewrite (models ht1 pht) as (models (fst res) pht);
      res
    }
    Clean -> {
      assert (pure (Used? v'));
      Pulse.Lib.Core.unreachable ()
    }
    Zombie -> {
      assert (pure (Used? v'));
      Pulse.Lib.Core.unreachable ()
    }
  }
}


#push-options "--fuel 1 --ifuel 2 --z3rlimit_factor 4"
fn insert
  (#kt:eqtype)
  (#vt:Type0)
  (ht:ht_t kt vt) (k:kt) (v:vt)
  (#pht:(p:erased (pht_t kt vt){PHT.not_full p.repr}))
  requires models ht pht
  returns b:(ht_t kt vt & bool)
  ensures
    exists* pht'.
      models (fst b) pht' **
      pure (same_sz_and_hashf (fst b) ht /\
            (if snd b
             then pht'==PHT.insert pht k v
             else pht'==reveal pht))
{
  let hashf = ht.hashf;
  let mut contents = ht.contents;

  unfold (models ht pht);

  let cidx = size_t_mod (hashf k) ht.sz;
  let mut off = 0sz;
  let mut cont = true;
  let mut idx = 0sz;

  while
  (
    let vcont = !cont;
    (vcont = true)
  )
  invariant b. exists* (voff:SZ.t) (vcont :bool) (vcontents:V.vec _) vidx s. (
    pts_to off voff **
    pts_to cont vcont **
    pts_to idx vidx **
    pts_to contents vcontents **
    V.pts_to vcontents s **
    pure (
      related ht pht /\
      V.is_full_vec vcontents /\
      SZ.(voff <=^ ht.sz) /\
      strong_all_used_not_by pht.repr (SZ.v cidx) (SZ.v voff) k /\
      walk pht.repr (SZ.v cidx) k (SZ.v voff) == lookup_repr pht.repr k /\
      insert_repr_walk #kt #vt #(pht_sz pht) #pht.spec pht.repr k v (SZ.v voff) (SZ.v cidx) () ()
        == insert_repr #kt #vt #(pht_sz pht) #pht.spec pht.repr k v /\

      ((not vcont) ==>  // insert succeeded
       (SZ.v vidx < Seq.length s /\
        (insert_repr #kt #vt #(pht_sz pht) #pht.spec pht.repr k v).seq `Seq.equal`
        Seq.upd s (SZ.v vidx) (mk_used_cell k v))) /\

      ((vcont) ==> s `Seq.equal` pht.repr.seq) /\  // insert failed

      b == (vcont = true)
    ))
  {
    let voff = !off;
    if (voff = ht.sz)
    {
      full_not_full pht.repr k;
      unreachable();
    }
    else
    {
      let sum = cidx `SZ.add` voff;
      let vidx = size_t_mod sum ht.sz;
      let c = V.replace_i_ref contents vidx Zombie;
      match c
      {
        Used k' v' -> {
          if (k' = k) {
            V.write_ref contents vidx (Used k' v');
            with vcontents. assert (pts_to contents vcontents);
            with s. assert (pts_to vcontents s);
            assert (pure (Seq.equal s pht.repr.seq));
            cont := false;
            idx := vidx;
            assert (pure ((insert_repr #kt #vt #(pht_sz pht) #pht.spec pht.repr k v).seq `Seq.equal`
                          Seq.upd pht.repr.seq (SZ.v vidx) (mk_used_cell k v)));
          } else {
            V.write_ref contents vidx (Used k' v');
            with vcontents. assert (pts_to contents vcontents);
            with s. assert (pts_to vcontents s);
            assert (pure (Seq.equal s pht.repr.seq));
            off := SZ.(voff +^ 1sz);
          };
        }
        Clean -> {
          V.write_ref contents vidx Clean;
          with vcontents. assert (pts_to contents vcontents);
          with s. assert (pts_to vcontents s);
          assert (pure (Seq.equal s pht.repr.seq));
          cont := false;
          idx := vidx;
          assert (pure ((insert_repr #kt #vt #(pht_sz pht) #pht.spec pht.repr k v).seq `Seq.equal`
                  Seq.upd pht.repr.seq (SZ.v vidx) (mk_used_cell k v)));
        }
        Zombie ->
        {
          with vcontents_g. assert (pts_to contents vcontents_g);
          with s. assert (pts_to vcontents_g s);
          assert (pure (Seq.equal s pht.repr.seq));
          let vcontents = !contents;
          let ht = { sz = ht.sz; hashf = hashf; contents = vcontents;};
          with s. rewrite (V.pts_to vcontents_g s) as (V.pts_to ht.contents s);
          fold (models ht pht);
          let res = lookup ht k;
          unfold (models (fst res) pht);
          contents := (fst res).contents;
          with s. rewrite (V.pts_to (fst res).contents s) as
                          (V.pts_to (reveal (hide (fst res).contents)) s);
          let o = snd res;
          match o
          {
            Some p ->
            {
              V.write_ref contents p Zombie;
              with s. rewrite (V.pts_to (reveal (hide (fst res).contents)) s)
                         as   (V.pts_to (fst res).contents s);
              with s. assert (V.pts_to (fst res).contents s);
              cont := false;
              idx := vidx;
              assert (pure ((insert_repr #kt #vt #(pht_sz pht) #pht.spec pht.repr k v).seq `Seq.equal`
                            Seq.upd (Seq.upd pht.repr.seq (SZ.v (p)) Zombie) (SZ.v vidx) (mk_used_cell k v)));
            }
            None ->
            {
              with s. rewrite (V.pts_to (reveal (hide (fst res).contents)) s)
                         as   (V.pts_to (fst res).contents s);
              with s. assert (V.pts_to (fst res).contents s);
              cont := false;
              idx := vidx;
              assert (pure ((insert_repr #kt #vt #(pht_sz pht) #pht.spec pht.repr k v).seq `Seq.equal`
                            Seq.upd pht.repr.seq (SZ.v vidx) (mk_used_cell k v)));
            }
          }

        }
      }
    }
  };

  let vcont = !cont;
  let vidx = !idx;

  if (vcont = false) {
    V.write_ref contents vidx (mk_used_cell k v);
    let vcontents = !contents;
    let ht = mk_ht ht.sz hashf vcontents;
    with vcontents. assert (pts_to contents vcontents);
    with s. assert (V.pts_to vcontents s);
    assert (pure (Seq.equal s (PHT.insert pht k v).repr.seq));
    rewrite (V.pts_to vcontents s) as (V.pts_to ht.contents s);
    let res = ((ht <: ht_t kt vt), true);
    fold (models ht (PHT.insert pht k v));
    with pht. rewrite (models ht pht) as (models (fst res) pht);
    res
  } else {
    let vcontents = !contents;
    let ht = mk_ht ht.sz hashf vcontents;
    let res = ((ht <: ht_t kt vt), false);
    with vcontents. assert (pts_to contents vcontents);
    with s. assert (V.pts_to vcontents s);
    rewrite (V.pts_to vcontents s) as (V.pts_to ht.contents s);
    fold (models ht pht);
    rewrite (models ht pht) as (models (fst res) pht);
    res
  }
}
#pop-options


let is_used
  (#[@@@ Rust_generics_bounds ["Copy"; "PartialEq"; "Clone"]] k:eqtype)
  (#[@@@ Rust_generics_bounds ["Clone"]] v:Type0)
  (c:cell k v) : (bool & cell k v) =
  match c with
  | Used _ _ -> true, c
  | _ -> false, c


fn not_full
  (#kt:eqtype)
  (#vt:Type0)
  (ht:ht_t kt vt)
  (#pht:erased (pht_t kt vt))

  requires models ht pht
  returns b:(ht_t kt vt & bool)
  ensures
    models (fst b) pht **
    pure (same_sz_and_hashf (fst b) ht /\ (snd b ==> PHT.not_full pht.repr))
{
  let hashf = ht.hashf;
  let mut contents = ht.contents;

  let mut i = 0sz;
  unfold (models ht pht);

  while
  (
    let vi = !i;
    if SZ.(vi <^ ht.sz)
    {
      let c = V.replace_i_ref contents vi Zombie;
      let b = is_used c;
      let _ = V.replace_i_ref contents vi (snd b);
      with vcontents. assert (pts_to contents vcontents);
      with s. assert (V.pts_to vcontents s);
      assert (pure (Seq.equal s pht.repr.seq));
      (fst b)
    }
    else
    {
      false
    }
  )
  invariant b. exists* (vi:SZ.t) vcontents. (
    pts_to contents vcontents **
    V.pts_to vcontents pht.repr.seq **
    pts_to i vi **
    pure (
      V.is_full_vec vcontents /\
      SZ.v ht.sz == pht_sz pht /\
      SZ.(vi <=^ ht.sz) /\
      (b == (SZ.(vi <^ ht.sz) && Used? (pht.repr @@ (SZ.v vi)))) /\
      (forall (i:nat). i < SZ.v vi ==> Used? (pht.repr @@ i))
    )
  )
  {
    let vi = !i;
    i := SZ.(vi +^ 1sz);
  };

  let vi = !i;
  let res = SZ.(vi <^ ht.sz);

  let vcontents = !contents;
  let ht = mk_ht ht.sz hashf vcontents;
  with vcontentsg. assert (pts_to contents vcontentsg);
  with s. rewrite (V.pts_to vcontentsg s) as (V.pts_to ht.contents s);
  fold (models ht pht);
  let b = ((ht <: ht_t kt vt), (res <: bool));
  rewrite (models ht pht) as (models (fst b) pht);
  b
}



fn insert_if_not_full
  (#kt:eqtype)
  (#vt:Type0)
  (ht:ht_t kt vt) (k:kt) (v:vt)
  (#pht:erased (PHT.pht_t kt vt))
  requires models ht pht
  returns b:(ht_t kt vt & bool)
  ensures
    exists* pht'.
      models (fst b) pht' **
      pure (same_sz_and_hashf (fst b) ht /\
            (if snd b
             then (PHT.not_full (reveal pht).repr /\
                   pht'==PHT.insert pht k v)
             else pht'==reveal pht))
{
  let b = not_full ht;
  if snd b
  {
    insert (fst b) k v
  }
  else
  {
    let res = (fst b, false);
    rewrite (models (fst b) pht) as (models (fst res) pht);
    res
  }
}

#push-options "--z3rlimit_factor 4"
fn delete
  (#kt:eqtype)
  (#vt:Type0)
  (ht:ht_t kt vt) (k:kt)
  (#pht:erased (pht_t kt vt))

  requires models ht pht
  returns b:(ht_t kt vt & bool)
  ensures
    (exists* pht'.
     models (fst b) pht' **
     pure (same_sz_and_hashf (fst b) ht /\
           (if snd b then pht' == PHT.delete pht k else pht' == reveal pht)))
{
  let hashf = ht.hashf;
  let mut contents = ht.contents;

  unfold (models ht pht);

  let cidx = size_t_mod (hashf k) ht.sz;
  let mut off = 0sz;
  let mut cont = true;
  let mut err = false;

  while
  (
    let vcont = !cont;
    let verr = !err;
    (vcont = true && verr = false)
  )
  invariant b. exists* (voff:SZ.t) (vcont verr:bool) (contents_v:V.vec _). (
    pts_to off voff **
    pts_to cont vcont **
    pts_to err verr **
    pts_to contents contents_v **
    V.pts_to contents_v (if (vcont || verr) then pht.repr.seq else (PHT.delete pht k).repr.seq) **
    pure (
      V.is_full_vec contents_v /\
      SZ.v ht.sz == pht_sz pht /\
      SZ.(voff <=^ ht.sz) /\
      all_used_not_by pht.repr (SZ.v cidx) (SZ.v voff) k /\
      walk pht.repr (SZ.v cidx) k (SZ.v voff) == lookup_repr pht.repr k /\
      delete_repr_walk #kt #vt #(pht_sz pht) #pht.spec pht.repr k (SZ.v voff) (SZ.v cidx) () ()
        == delete_repr #kt #vt #(pht_sz pht) #pht.spec pht.repr k /\
      b == (vcont = true && verr = false)
    ))
  {
    with vcont. assert (pts_to cont vcont);
    let voff = !off;
    if (voff = ht.sz)
    {
      cont := false;
      rewrite each vcont as false; // also relying on #110
    }
    else
    {
      let sum = cidx `SZ.add` voff;
      let idx = size_t_mod sum ht.sz;
      let c = V.read_ref contents idx;
      match c
      {
        Used k' v' ->
        {
          if (k' = k)
          {
            V.write_ref contents idx Zombie;
            cont := false;
            assert (pure (pht.repr @@ SZ.v idx == Used k v'));
            assert (pure (Seq.upd pht.repr.seq (SZ.v idx) Zombie
              `Seq.equal` (PHT.delete pht k).repr.seq));
          }
          else
          {
            off := SZ.(voff +^ 1sz);
          }
        }
        Clean ->
        {
          cont := false;
          assert (pure (pht.repr == (PHT.delete pht k).repr));
          rewrite each vcont as false; // also relying on #110
        }
        Zombie ->
        {
          off := SZ.(voff +^ 1sz);
        }
      }
    }
  };

  with contents_v_g. assert (pts_to contents contents_v_g);
  let contents_v = !contents;
  let ht = mk_ht ht.sz hashf contents_v;
  with s. rewrite (V.pts_to contents_v_g s) as (V.pts_to ht.contents s);

  let verr = !err;
  if verr
  {
    let res = ((ht <: ht_t kt vt), false);
    fold (models ht pht);
    rewrite (models ht pht) as (models (fst res) pht);
    res
  }
  else
  {
    let res = ((ht <: ht_t kt vt), true);
    fold (models ht (PHT.delete pht k));
    rewrite (models ht (PHT.delete pht k)) as (models (fst res) (PHT.delete pht k));
    res
  }
}
#pop-options

// 
// fn test_mono ()
//   requires emp
//   ensures emp
// {
//    let htc = alloc #SZ.t #SZ.t hash_us 128sz;
//    with pht. assert (models htc pht);
//    let ht = R.alloc htc;
//    init_not_full #SZ.t #SZ.t hash_us 128sz;
//    rewrite (models htc pht) as (models (reveal (hide htc)) pht);
//    let b = insert ht 0sz 17sz;
//    if (b) {
//      let v = lookup ht 0sz;
//      if (fst v) {
//        assert pure (snd v == Some 17sz);
//        R.free ht;
//        with pht. assert (models (reveal (hide htc)) pht);
//        rewrite (models (reveal (hide htc)) pht) as (models htc pht);
//        dealloc htc
//      }
//      else {
//       R.free ht;
//       with pht. assert (models (reveal (hide htc)) pht);
//       rewrite (models (reveal (hide htc)) pht) as (models htc pht);
//       dealloc htc
//      }
//    }
//    else {
//     let b = delete ht 0sz;
//     let b' = not_full ht;
//     R.free ht;
//     with pht. assert (models (reveal (hide htc)) pht);
//     rewrite (models (reveal (hide htc)) pht) as (models htc pht);
//     dealloc htc
//    }
// }
// 
