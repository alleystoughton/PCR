(* Inj.ec *)

(* Injective Maps *)

require import AllCore NewFMap FSet.

pred inj (mp : ('a, 'b)fmap, ran : 'b fset) =
  rng mp = ran /\
  (forall (x1 x2 : 'a),
   mem (dom mp) x1 => mem (dom mp) x2 =>
   oget mp.[x1] = oget mp.[x2] =>
   x1 = x2).

lemma inj_empty : inj map0<:'a,'b> fset0<:'b>.
proof.
split; first apply rng0.
move => x1 x2; by rewrite dom0 in_fset0.
qed.

lemma inj_add (mp : ('a, 'b)fmap, ran : 'b fset, x : 'a, y : 'b) :
  inj mp ran => ! mem (dom mp) x => ! mem ran y =>
  inj mp.[x <- y] (ran `|` fset1 y).
proof.
move => [rng_mp inj_mp] not_mem_dom_mp_x not_mem_ran_y.
split; first by rewrite rng_set rem_id // rng_mp.
move => x1 x2.
rewrite 2!domP 2!in_fsetU =>
  mem_dom_mp_x1_or_eq_x_x1 mem_dom_mp_x2_or_eq_x_x2
  eq_lookup_x1_x2_mp_upd_x_y.
rewrite in_fset1 in mem_dom_mp_x1_or_eq_x_x1.
rewrite in_fset1 in mem_dom_mp_x2_or_eq_x_x2.
case (x1 = x) => [->> | ne_x1_x].
case (x2 = x) => [->> // | ne_x2_x].
rewrite 2!getP /= oget_some in eq_lookup_x1_x2_mp_upd_x_y.
move : eq_lookup_x1_x2_mp_upd_x_y; rewrite ne_x2_x /= => eq_y_lookup_mp_x2.
have /# : mem (rng mp) y.
  rewrite in_rng; exists x2; rewrite eq_y_lookup_mp_x2 -some_oget 1:-in_dom /#.
case (x2 = x) => [->> // | ne_x2_x].
rewrite 2!getP ne_x1_x /= oget_some in eq_lookup_x1_x2_mp_upd_x_y.
have /# : mem (rng mp) y.
  rewrite in_rng; exists x1.
  rewrite -eq_lookup_x1_x2_mp_upd_x_y -some_oget 1:-in_dom /#.
move : eq_lookup_x1_x2_mp_upd_x_y; rewrite 2!getP ne_x1_x ne_x2_x /= /#.
qed.

lemma inj_cancel (mp : ('a, 'b)fmap, ran : 'b fset, x y : 'a) :
  inj mp ran => mem (dom mp) x => mem (dom mp) y =>
  oget mp.[x] = oget mp.[y] => x = y.
proof.
move => [_ inj_mp] mem_dom_mp_x mem_dom_mp_y eq_get_mp_xy.
by apply inj_mp.
qed.

lemma inj_cancel_contra (mp : ('a, 'b)fmap, ran : 'b fset, x y : 'a) :
  inj mp ran => mem (dom mp) x => mem (dom mp) y =>
  x <> y => oget mp.[x] <> oget mp.[y].
proof.
move => inj_mp_ran mem_dom_mp_x mem_dom_mp_y ne_xy.
case (oget mp.[x] = oget mp.[y]) => [eq_get_mp_xy | //].
have // : x = y by apply (inj_cancel mp ran x y).
qed.
