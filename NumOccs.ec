(* NumOccs.ec *)

(* Operators for Counting Numbers of Occurrences of Elements in Lists *)

prover quorum=2 ["Alt-Ergo" "Z3"].  (* both Alt-Ergo and Z3 must succeed *)

require import AllCore List StdRing.

(* if 0 <= n <= size ys, then num_occs_upto x ys n is the number of
   occurrences of x in the first n elements of ys *)

op num_occs_upto (x : 'a) (ys : 'a list) (n : int) : int =
  with ys = "[]"      => 0
  with ys = (::) y ys =>
    if n = 0
    then 0
    else (if x = y then 1 else 0) + num_occs_upto x ys (n - 1).

lemma num_occs_upto0 (x : 'a, ys : 'a list) : num_occs_upto x ys 0 = 0.
proof. elim ys; trivial. qed.

lemma num_occs_upto_eq (x : 'a, ys : 'a list, i : int) :
  0 <= i < size ys => nth x ys i = x =>
  num_occs_upto x ys (i + 1) = num_occs_upto x ys i + 1.
proof.
move : i; elim ys => [/# | y ys IH i /= z_le_i_lt_sz_ys_plus1 nth_eq].
case (i = 0) => [->> /= | ne0_i].
have -> /= : x = y by smt().
by rewrite num_occs_upto0.
have z_le_i_min1_lt_sz_ys : 0 <= i - 1 < size ys by smt().
have -> /= : i + 1 <> 0 by smt().
move : nth_eq; rewrite ne0_i /= => nth_eq.
by rewrite -(addzA _ _ 1) -(IH (i - 1)) // -(addzA _ _ (-1))
           -(addzA _ _ 1).
qed.

lemma num_occs_upto_ne (x : 'a, ys : 'a list, i : int) :
  0 <= i < size ys => nth x ys i <> x =>
  num_occs_upto x ys (i + 1) = num_occs_upto x ys i.
proof.
move : i; elim ys => [// | y ys IH i z_le_i_lt_sz_y_ys nth_eq].
case (i = 0) => [->> /= | ne0_i].
rewrite /= eq_sym in nth_eq.
by rewrite nth_eq /= num_occs_upto0.
have z_le_i_min1_lt_sz_ys : 0 <= i - 1 < size ys by smt().
have -> /= : i + 1 <> 0 by smt().
move : nth_eq.
rewrite -cat1s nth_cat /=.
have -> /= : ! i < 1 by smt().
move => nth_eq.
by rewrite -(IH (i - 1)) // ne0_i.
qed.

lemma num_occs_upto_ge0 (x : 'a, ys : 'a list, i : int) :
  0 <= i <= size ys => 0 <= num_occs_upto x ys i.
proof.
have gen :
  forall (j : int),
  0 <= j => j <= size ys => 0 <= num_occs_upto x ys j.
  elim => [| j ge0_j IH j_plus1_le_sz_ys].
  by rewrite num_occs_upto0.
  have j_lt_sz_ys : j < size ys by rewrite -lez_add1r addzC.
  case (nth x ys j = x) => [nth_eq | nth_ne].
  rewrite num_occs_upto_eq //#.
  rewrite num_occs_upto_ne //#.
move => [ge0_i lt_i_sz_ys].
by apply gen.
qed.

lemma num_occs_upto_0overall_imp_0all_but_last
      (x : 'a, ys : 'a list, i : int) :
  0 <= i < size ys =>
  num_occs_upto x ys (i + 1) = 0 =>
  num_occs_upto x ys i = 0.
proof.
move => z_le_i_lt_sz_ys.
case (nth x ys i = x) => [nth_eq | nth_ne].
rewrite num_occs_upto_eq //.
smt(num_occs_upto_ge0).
by rewrite num_occs_upto_ne.
qed.

lemma num_occs_upto_0overall_imp_ne_last (x : 'a, ys : 'a list, i : int) :
  0 <= i < size ys =>
  num_occs_upto x ys (i + 1) = 0 =>
  nth x ys i <> x.
proof.
move => z_le_i_lt_sz_ys.
case (nth x ys i = x) => // nth_eq_x.
rewrite num_occs_upto_eq //.
smt(num_occs_upto_ge0).
qed.

lemma num_occs_upto_drop_last_part (x : 'a, ys, zs : 'a list) :
  num_occs_upto x (ys ++ zs) (size ys) = num_occs_upto x ys (size ys).
proof.
have gen :
  forall (i : int),
  0 <= i => i <= size ys =>
  num_occs_upto x (ys ++ zs) i = num_occs_upto x ys i.
  elim => [| i ge0_i IH i_plus1_le_sz_ys].
  by rewrite 2!num_occs_upto0.
  have i_lt_sz_ys : i < size ys by rewrite -lez_add1r addzC.
  case (nth x ys i = x) => [nth_eq | nth_ne].
  rewrite num_occs_upto_eq 1:size_cat.
  smt(size_ge0).
  by rewrite nth_cat i_lt_sz_ys.
  by rewrite num_occs_upto_eq // IH 1:ltzW.
  rewrite num_occs_upto_ne 1:size_cat.
  smt(size_ge0).
  by rewrite nth_cat i_lt_sz_ys.
  by rewrite num_occs_upto_ne // IH 1:ltzW.
by rewrite gen 1:size_ge0.
qed.

(* num_occs x ys is the number of occurrences of x in ys *)

op num_occs (x : 'a) (ys : 'a list) : int = num_occs_upto x ys (size ys).

lemma num_occs_not_mem_imp0 (x : 'a, ys : 'a list) :
  ! mem ys x => num_occs x ys = 0.
proof.
move => not_mem_ys_x.
have gen :
  forall (i : int), 0 <= i => i <= size ys => num_occs_upto x ys i = 0.
  elim => [| i ge0_i IH i_plus1_le_sz_ys].
  by rewrite num_occs_upto0.
  have i_lt_sz_ys : i < size ys by rewrite -lez_add1r addzC.
  case (nth x ys i = x) => [nth_eq | nth_ne].
  have // : mem ys x by rewrite -nth_eq mem_nth.
  by rewrite num_occs_upto_ne // IH 1:ltzW.
by rewrite /num_occs gen 1:size_ge0.
qed.

lemma num_occs_zero_imp_notmem (x : 'a, ys : 'a list) :
  num_occs x ys = 0 => ! mem ys x.
proof.
have gen :
  forall (i : int),
  0 <= i => i <= size ys => num_occs_upto x ys i = 0 =>
  !(exists (j : int),
    0 <= j /\ j < i /\ nth x ys j = x).
  elim => [_ _ |].
  case (exists (j : int), 0 <= j /\ j < 0 /\ nth x ys j = x) => //#.
  move => i ge0_i IH i_plus1_le_sz_ys overall0.
  have i_lt_sz_ys : i < size ys by rewrite -lez_add1r addzC.
  case (nth x ys i = x) => [nth_eq | nth_ne].
  move : overall0 => overall0.
  rewrite num_occs_upto_eq // in overall0.
  smt(num_occs_upto_ge0).
  have overall0_all_but_last : num_occs_upto x ys i = 0
    by rewrite num_occs_upto_0overall_imp_0all_but_last.
  have IHres := IH _ _; [by rewrite ltzW | trivial |].
  smt().
rewrite /num_occs => overall0.
have gen_app := gen (size ys) _ _ _; [apply size_ge0 | trivial | trivial |].
case (mem ys x) => // mem_ys_x.
have // :
  exists (j : int), 0 <= j /\ j < size ys /\ nth x ys j = x.
  exists (index x ys).
  split; first apply index_ge0.
  split; first by rewrite index_mem.
  by rewrite nth_index.
qed.

lemma num_occs_nil (x : 'a) : num_occs x [] = 0.
proof. trivial. qed.

lemma num_occs_sing (x y : 'a) :
  num_occs x [y] = if x = y then 1 else 0.
proof. trivial. qed.

lemma num_occs_cons (x y : 'a) (zs : 'a list) :
  num_occs x (y :: zs) =
  (if x = y then 1 else 0) + num_occs x zs.
proof.
rewrite /num_occs.
case (x = y) => -> /=; have -> /= : 1 + size zs <> 0; by smt(size_ge0).
qed.

lemma num_occs_cat (x : 'a) (ys zs : 'a list) :
  num_occs x (ys ++ zs) = num_occs x ys + num_occs x zs.
proof.
elim ys => [/= | y ys IH].
by rewrite num_occs_nil.
case (x = y) => [->> /= | ne_xy].
by rewrite 2!num_occs_cons /= IH addzA.
by rewrite 2!num_occs_cons /= ne_xy /= IH.
qed.

lemma num_occs_add_end (x y : 'a) (zs : 'a list) :
  num_occs x (zs ++ [y]) =
  num_occs x zs + (if x = y then 1 else 0).
proof. by rewrite num_occs_cat num_occs_cons. qed.
