(* ElemsCounts.ec *)

(* Finite Maps Providing Counts for Certain Elements *)

require import AllCore FSet NewFMap FMapAux.

(* counts for certain elements; counts are always >= 1 *)

type 'a counts = ('a, int)fmap.

(* empty elements counts map *)

op empty_counts : 'a counts = map0.

(* when looking up a count, the result is 0 when not in map's domain *)

op get_count (cnts : 'a counts) (elem : 'a) : int =
  if mem (dom cnts) elem then oget cnts.[elem] else 0.

(* when incrementing a count, if the element isn't already in the
   map's domain, we start at 1 *)

op incr_count (cnts : 'a counts) (elem : 'a) : 'a counts =
  if mem (dom cnts) elem
  then cnts.[elem <- oget(cnts.[elem]) + 1]
  else cnts.[elem <- 1].

(* lemmas about elements counts maps *)

lemma ec_incr_mem_eq (cnts : 'a counts, elem : 'a) :
  mem (dom cnts) elem =>
  incr_count cnts elem =
  cnts.[elem <- oget(cnts.[elem]) + 1].
proof. rewrite /incr_count; by move => ->. qed.

lemma ec_incr_not_mem_eq (cnts : 'a counts, elem : 'a) :
  ! mem (dom cnts) elem =>
  incr_count cnts elem = cnts.[elem <- 1].
proof. rewrite /incr_count; by move => ->. qed.

lemma ec_incr_dom (cnts : 'a counts) (elem : 'a) :
  dom(incr_count cnts elem) = dom cnts `|` fset1 elem.
proof.
rewrite /incr_count.
case (mem (dom cnts) elem) => [mem_elem | not_mem_elem];
by rewrite dom_set.
qed.

lemma ec_get_not_in_dom (cnts : 'a counts) (elem : 'a) :
  ! mem (dom cnts) elem => get_count cnts elem = 0.
proof. smt(). qed.

lemma ec_get_in_dom (cnts : 'a counts) (elem : 'a) :
  mem (dom cnts) elem =>
  get_count cnts elem = oget cnts.[elem].
proof. smt(). qed.

lemma ec_get_empty (elem : 'a) :
  get_count empty_counts elem = 0.
proof. by rewrite /get_count /empty_count dom0 in_fset0. qed.

lemma ec_incr_oget_not_in_dom_eq (cnts : 'a counts) (elem : 'a) :
  ! mem (dom cnts) elem =>
  oget (incr_count cnts elem).[elem] = 1.
proof.
move => not_mem_dom_ec_elem; rewrite /incr_count.
by rewrite not_mem_dom_ec_elem /= getP_eq oget_some.
qed.

lemma ec_incr_oget_in_dom_eq (cnts : 'a counts) (elem : 'a) :
  mem (dom cnts) elem =>
  oget (incr_count cnts elem).[elem] = oget cnts.[elem] + 1.
proof.
move => mem_dom_ec_elem; rewrite /incr_count.
case (mem (dom cnts) elem) => [mem_elem | not_mem_elem];
  by rewrite getP /= oget_some.
qed.

lemma ec_incr_get_eq (cnts : 'a counts) (elem : 'a) :
  get_count (incr_count cnts elem) elem =
  get_count cnts elem + 1.
proof.
rewrite /get_count.
case (mem (dom cnts) elem) => [mem | not_mem].
by rewrite ec_incr_dom in_fsetU in_fset1 /= ec_incr_oget_in_dom_eq.
by rewrite ec_incr_dom in_fsetU in_fset1 /= /incr_count not_mem /= getP.
qed.

lemma ec_incr_oget_in_dom_ne (cnts : 'a counts) (elem elem' : 'a) :
  elem' <> elem => mem (dom cnts) elem' =>
  oget (incr_count cnts elem).[elem'] = oget cnts.[elem'].
proof.
move => ne_elem'_elem mem_dom_ec_elem'; rewrite /incr_count.
case (mem (dom cnts) elem) => [mem_elem | not_mem_elem];
  by rewrite getP ne_elem'_elem.
qed.

lemma ec_incr_get_ne (cnts : 'a counts) (elem elem' : 'a) :
  elem' <> elem =>
  get_count (incr_count cnts elem) elem' =
  get_count cnts elem'.
proof.
move => ne_elem'_elem; rewrite /get_count.
rewrite ec_incr_dom in_fsetU in_fset1 ne_elem'_elem /=.
case (mem (dom cnts) elem') => [mem_dom_ec_elem' | //];
  by apply ec_incr_oget_in_dom_ne.
qed.

lemma incr_count_swap (cnts : 'a counts, elem1 elem2 : 'a) :
  incr_count (incr_count cnts elem1) elem2 =
  incr_count (incr_count cnts elem2) elem1.
proof.
case (elem1 = elem2) => [-> // | ne_elem1_elem2].
case (mem (dom cnts) elem1) => [mem_ec_1 | not_mem_ec_1].
case (mem (dom cnts) elem2) => [mem_ec_2 | not_mem_ec_2].
do 2! rewrite (ec_incr_mem_eq cnts _) //.
do 2! rewrite ec_incr_mem_eq 1:domP 1:in_fsetU1 1:/#.
rewrite 2!getP ne_elem1_elem2; have -> /= : elem2 <> elem1 by smt().
smt(set_set).
rewrite (ec_incr_mem_eq cnts elem1) //.
rewrite (ec_incr_not_mem_eq cnts elem2) //.
rewrite (ec_incr_not_mem_eq _ elem2) 1:domP 1:in_fsetU1 1:/#.
rewrite (ec_incr_mem_eq _ elem1) // 1:domP 1:in_fsetU1 1:/#.
rewrite set_set ne_elem1_elem2 /=.
by rewrite getP ne_elem1_elem2.
case (mem (dom cnts) elem2) => [mem_ec_2 | not_mem_ec_2].
rewrite (ec_incr_mem_eq cnts elem2) //.
rewrite (ec_incr_not_mem_eq cnts elem1) //.
rewrite (ec_incr_not_mem_eq _ elem1) 1:domP 1:in_fsetU1 1:/#.
rewrite (ec_incr_mem_eq _ elem2) // 1:domP 1:in_fsetU1 1:/#.
rewrite (set_set _ elem2 elem1); have -> // : elem2 <> elem1 by smt().
rewrite getP; by have -> : elem2 <> elem1 by smt().
do 2! rewrite (ec_incr_not_mem_eq cnts) //.
do 2! rewrite ec_incr_not_mem_eq 1:domP 1:in_fsetU1 1:/#.
smt(set_set).
qed.

(* predicate preserved by incr_count *)

pred dom_pos (cnts : 'a counts) =
  forall (elem : 'a),
  mem (dom cnts) elem => 1 <= oget(cnts.[elem]).

lemma dom_pos_empty : dom_pos empty_counts<:'a>.
proof.
move => elem.
by rewrite dom0 in_fset0.
qed.

lemma dom_pos_incr (cnts : 'a counts, elem : 'a) :
  dom_pos cnts => dom_pos (incr_count cnts elem).
proof.
move => @/dom_pos dom_pos_ec elem' mem_incr_ec_elem_elem'.
rewrite ec_incr_dom in_fsetU1 in mem_incr_ec_elem_elem'.
elim mem_incr_ec_elem_elem' => [mem_ec_elem' | ->].
have dom_pos_ec_elem' := dom_pos_ec elem' mem_ec_elem'.
case (elem' = elem) => [<- | ne_elem'_elem].
rewrite ec_incr_oget_in_dom_eq /#.
by rewrite ec_incr_oget_in_dom_ne.
case (mem (dom cnts) elem) => [mem_ec_elem | not_mem_ec_elem].
rewrite ec_incr_oget_in_dom_eq /#.
by rewrite ec_incr_oget_not_in_dom_eq.
qed.

lemma counts_eq (cnts1 cnts2 : 'a counts) :
  dom_pos cnts1 => dom_pos cnts2 =>
  (forall (elem : 'a),
   get_count cnts1 elem = get_count cnts2 elem) =>
  cnts1 = cnts2.
proof.
move => dom_pos_ec1 dom_pos_ec2 get_count_eq.
apply fmapP => elem.
case (mem (dom cnts1) elem) => [mem_dom1_elem | not_mem_dom1_elem].
case (mem (dom cnts2) elem) => [mem_dom2_elem | not_mem_dom2_elem].
have get_count_eq_elem := get_count_eq elem.
rewrite ec_get_in_dom // in get_count_eq_elem.
rewrite ec_get_in_dom // in get_count_eq_elem.
rewrite (get_oget cnts1) // (get_oget cnts2) //.
smt().
case (mem (dom cnts2) elem) => [mem_dom2_elem | not_mem_dom2_elem].
smt().
have get_count_eq_elem := get_count_eq elem.
by rewrite get_none // get_none.
qed.
