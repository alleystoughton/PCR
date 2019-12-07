(* Inj.ec *)

(* Injective Maps *)

prover [""].  (* no SMT solvers *)

require import AllCore SmtMap FSet MapAux.

pred inj (mp : ('a, 'b) fmap, ran : 'b fset) =
  frng mp = ran /\
  (forall (x1 x2 : 'a),
   x1 \in mp => x2 \in mp =>
   oget mp.[x1] = oget mp.[x2] =>
   x1 = x2).

lemma inj_empty : inj empty<:'a,'b> fset0<:'b>.
proof.
split; [apply frng0 | move => x1 x2; by rewrite mem_empty].
qed.

lemma inj_add (mp : ('a, 'b) fmap, ran : 'b fset, x : 'a, y : 'b) :
  inj mp ran => x \notin mp => ! mem ran y =>
  inj mp.[x <- y] (ran `|` fset1 y).
proof.
move => [rng_mp inj_mp] not_x_in_mp not_y_in_rng.
split; first by rewrite frng_set rem_id // rng_mp.
move => x1 x2.
rewrite 2!mem_set 2!get_setE.
elim => [x1_in_mp | -> /=].
elim => [x2_in_mp | -> /=].
case (x1 = x) => [ ->> // | ne_x1_x].
case (x2 = x) => [ ->> // | ne_x2_x].
by apply inj_mp.
case (x1 = x) => [// | ne_x1_x get_x1_y].
have // : y \in ran.
  rewrite -rng_mp mem_frng rngE /=.
  exists x1; by rewrite (get_some mp x1).
elim => //.
case (x2 = x) => [<<- // | ne_x2_x x2_in_mp].
rewrite eq_sym; move => get_x2_eq_y.
have // : y \in ran.
  rewrite -rng_mp mem_frng rngE /=.
  exists x2; by rewrite (get_some mp x2).
qed.

lemma inj_cancel (mp : ('a, 'b) fmap, ran : 'b fset, x y : 'a) :
  inj mp ran => x \in mp => y \in mp =>
  oget mp.[x] = oget mp.[y] => x = y.
proof.
move => [_ inj_mp] x_in_mp y_in_mp eq_get_mp_xy.
by apply inj_mp.
qed.

lemma inj_cancel_contra (mp : ('a, 'b) fmap, ran : 'b fset, x y : 'a) :
  inj mp ran => x \in mp => y \in mp =>
  x <> y => oget mp.[x] <> oget mp.[y].
proof.
move => inj_mp_ran x_in_mp y_in_mp ne_xy.
case (oget mp.[x] = oget mp.[y]) => [eq_get_mp_xy | //].
have // : x = y by apply (inj_cancel mp ran x y).
qed.
