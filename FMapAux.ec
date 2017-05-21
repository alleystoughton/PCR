(* FMapAux.ec *)

(* Auxiliary Lemmas on Finite Maps *)

require import FSet NewFMap.

lemma not_in_dom (m : ('a, 'b)fmap, x : 'a) :
  ! mem (dom m) x <=> m.[x] = None.
proof. by rewrite in_dom. qed.

lemma get_none (m : ('a, 'b)fmap, x : 'a) :
  ! mem (dom m) x => m.[x] = None.
proof. by move => /not_in_dom. qed.
