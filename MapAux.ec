(* MapAux.ec *)

(* Auxiliary Lemmas on Maps *)

prover [""].  (* no SMT solvers *)

require import AllCore SmtMap FSet.

lemma get_none (mp : ('a, 'b) fmap, x : 'a) :
  x \notin mp => mp.[x] = None.
proof. by rewrite domE. qed.

lemma get_some (mp : ('a, 'b) fmap, x : 'a) :
  x \in mp => mp.[x] = Some (oget mp.[x]).
proof. move => /domE; by case mp.[x]. qed.

lemma set_same (mp : ('a, 'b) fmap, x : 'a) :
  x \in mp => mp.[x <- oget mp.[x]] = mp.
proof.
move => x_in_mp.
apply fmap_eqP => y.
case (y = x) => [->> | ne_y_x].
by rewrite get_set_sameE get_some.
by rewrite get_setE ne_y_x.
qed.

lemma frng_set (mp : ('a, 'b) fmap, x : 'a, y : 'b) :
  frng mp.[x <- y] = frng (rem mp x) `|` fset1 y.
proof.
apply fsetP => z; rewrite in_fsetU in_fset1 2!mem_frng 2!rngE /=.
split => [[x'] | [[x'] | ->]].
case (x' = x) => [-> | ne_x'_x].
by rewrite get_set_sameE /= => ->.
rewrite get_setE ne_x'_x /= => get_x'_some_z.
left; exists x'; by rewrite remE ne_x'_x.
rewrite remE.
case (x' = x) => // ne_x'_x get_x'_some_z.
exists x'; by rewrite get_setE ne_x'_x.
exists x; by rewrite get_set_sameE.
qed.

lemma eq_except_ne_in (x y : 'a, mp1 mp2 : ('a, 'b) fmap) :
  eq_except (pred1 x) mp1 mp2 => y <> x =>
  y \in mp1 => y \in mp2.
proof.
move => /eq_exceptP @/pred1 eq_exc ne_y_x.
by rewrite 2!domE eq_exc.
qed.

lemma rem_id (mp : ('a, 'b) fmap, x : 'a) :
  x \notin mp => rem mp x = mp.
proof.
move => x_notin_mp; apply fmap_eqP => y; rewrite remE.
case (y = x) => // ->.
case (None = mp.[x]) => // get_not_none.
rewrite eq_sym -domE // in get_not_none.
qed.
