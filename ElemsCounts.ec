(* ElemsCounts.ec *)

(* Finite Maps Providing Counts for Certain Elements *)

require import AllCore FSet SmtMap MapAux.

(* counts for certain elements; counts are always >= 1 *)

type 'a counts = ('a, int) fmap.

(* empty elements counts map *)

op empty_counts : 'a counts = empty.

(* when looking up a count, the result is 0 when not in map's domain *)

op get_count (cnts : 'a counts) (elem : 'a) : int =
  if elem \in cnts then oget cnts.[elem] else 0.

(* when incrementing a count, if the element isn't already in the
   map's domain, we start at 1 *)

op incr_count (cnts : 'a counts) (elem : 'a) : 'a counts =
  if elem \in cnts
  then cnts.[elem <- oget(cnts.[elem]) + 1]
  else cnts.[elem <- 1].

(* lemmas about elements counts maps *)

lemma ec_incr_mem_eq (cnts : 'a counts, elem : 'a) :
  elem \in cnts =>
  incr_count cnts elem =
  cnts.[elem <- oget(cnts.[elem]) + 1].
proof. rewrite /incr_count; by move => ->. qed.

lemma ec_incr_not_mem_eq (cnts : 'a counts, elem : 'a) :
  ! elem \in cnts =>
  incr_count cnts elem = cnts.[elem <- 1].
proof. rewrite /incr_count; by move => ->. qed.

lemma ec_incr_dom (cnts : 'a counts) (elem : 'a) :
  fdom(incr_count cnts elem) = fdom cnts `|` fset1 elem.
proof.
rewrite /incr_count.
case (elem \in cnts) => [elem_in_cnts | elem_not_in_cnts];
by rewrite fdom_set.
qed.

lemma ec_get_not_in_dom (cnts : 'a counts) (elem : 'a) :
  ! elem \in cnts => get_count cnts elem = 0.
proof. rewrite /get_count; by move => ->. qed.

lemma ec_get_in_dom (cnts : 'a counts) (elem : 'a) :
  elem \in cnts => get_count cnts elem = oget cnts.[elem].
proof. rewrite /get_count; by move => ->. qed.

lemma ec_get_empty (elem : 'a) :
  get_count empty_counts elem = 0.
proof. by rewrite /get_count /empty_count mem_empty. qed.

lemma ec_incr_oget_not_in_dom_eq (cnts : 'a counts) (elem : 'a) :
  ! elem \in cnts => oget (incr_count cnts elem).[elem] = 1.
proof.
move => elem_not_in_cnts; rewrite /incr_count.
by rewrite elem_not_in_cnts /= get_set_sameE oget_some.
qed.

lemma ec_incr_oget_in_dom_eq (cnts : 'a counts) (elem : 'a) :
  elem \in cnts =>
  oget (incr_count cnts elem).[elem] = oget cnts.[elem] + 1.
proof.
rewrite /incr_count; move => -> /=.
by rewrite get_setE /= oget_some.
qed.

lemma ec_incr_get_eq (cnts : 'a counts) (elem : 'a) :
  get_count (incr_count cnts elem) elem =
  get_count cnts elem + 1.
proof.
rewrite /get_count.
case (elem \in cnts) => [elem_in_cnts | elem_not_in_cnts].
by rewrite -mem_fdom ec_incr_dom in_fsetU in_fset1 /= ec_incr_oget_in_dom_eq.
by rewrite -mem_fdom ec_incr_dom in_fsetU in_fset1 /=
           /incr_count elem_not_in_cnts /= get_set_sameE.
qed.

lemma ec_incr_oget_in_dom_ne (cnts : 'a counts) (elem elem' : 'a) :
  elem' <> elem => elem' \in cnts =>
  oget (incr_count cnts elem).[elem'] = oget cnts.[elem'].
proof.
move => ne_elem'_elem elem'_in_cnts; rewrite /incr_count.
rewrite eq_sym in ne_elem'_elem.
case (elem \in cnts) => [elem_in_cnts | elem_not_in_cnts];
  by rewrite get_setE (eq_sym elem') ne_elem'_elem.
qed.

lemma ec_incr_get_ne (cnts : 'a counts) (elem elem' : 'a) :
  elem' <> elem =>
  get_count (incr_count cnts elem) elem' =
  get_count cnts elem'.
proof.
move => ne_elem'_elem; rewrite /get_count.
rewrite -mem_fdom ec_incr_dom in_fsetU in_fset1 ne_elem'_elem /=
         mem_fdom.
case (elem' \in cnts) => [elem'_in_cnts | //].
by apply ec_incr_oget_in_dom_ne.
qed.

lemma incr_count_swap (cnts : 'a counts, elem1 elem2 : 'a) :
  incr_count (incr_count cnts elem1) elem2 =
  incr_count (incr_count cnts elem2) elem1.
proof.
case (elem1 = elem2) => [-> // | ne_elem1_elem2].
case (elem1 \in cnts) => [elem1_in_cnts | elem1_not_in_cnts].
case (elem2 \in cnts) => [elem2_in_cnts | elem2_not_in_cnts].
do 2! rewrite (ec_incr_mem_eq cnts _) //.
rewrite ec_incr_mem_eq 1:domE get_setE (eq_sym elem2) ne_elem1_elem2 //.
by rewrite ec_incr_mem_eq 1:domE get_setE ne_elem1_elem2 //= fmapSS_neqE
           1:(eq_sym elem2) //.
by rewrite (ec_incr_mem_eq cnts elem1) // (ec_incr_not_mem_eq cnts elem2) //
           (ec_incr_not_mem_eq _ elem2) 1:domE 1:get_setE 1:(eq_sym elem2)
           1:ne_elem1_elem2 // ec_incr_mem_eq 1:domE get_setE
           ne_elem1_elem2 //= fmapSS_neqE 1:(eq_sym elem2).
case (elem2 \in cnts) => [elem2_in_cnts | elem2_not_in_cnts].
by rewrite (ec_incr_mem_eq cnts elem2) // (ec_incr_not_mem_eq cnts elem1) //
           (ec_incr_not_mem_eq _ elem1) 1:domE 1:get_setE 1:ne_elem1_elem2 //
           ec_incr_mem_eq 1:domE get_setE 1:(eq_sym elem2) 1:ne_elem1_elem2 //=
           fmapSS_neqE 1:(eq_sym elem2) // 1:(eq_sym elem2) ne_elem1_elem2.
by rewrite (ec_incr_not_mem_eq cnts elem1) // (ec_incr_not_mem_eq cnts elem2) //
           ec_incr_not_mem_eq 1:domE 1:get_setE 1:(eq_sym elem2) 1:ne_elem1_elem2 //
           ec_incr_not_mem_eq 1:domE 1:get_setE 1:ne_elem1_elem2 //
           fmapSS_neqE 1:(eq_sym elem2) 1:ne_elem1_elem2.
qed.

(* predicate preserved by incr_count *)

pred dom_pos (cnts : 'a counts) =
  forall (elem : 'a),
  elem \in cnts => 1 <= oget(cnts.[elem]).

lemma dom_pos_empty : dom_pos empty_counts<:'a>.
proof. move => elem; by rewrite mem_empty. qed.

lemma dom_pos_incr (cnts : 'a counts, elem : 'a) :
  dom_pos cnts => dom_pos (incr_count cnts elem).
proof.
move => @/dom_pos dom_pos_ec elem' elem'_in_incr_cnts_elem.
rewrite -mem_fdom ec_incr_dom in_fsetU mem_fdom
        in_fset1 in elem'_in_incr_cnts_elem.
elim elem'_in_incr_cnts_elem => [elem'_in_cnts | ->].
have dom_pos_ec_elem' := dom_pos_ec elem' elem'_in_cnts.
case (elem' = elem) => [<- | ne_elem'_elem].
rewrite ec_incr_oget_in_dom_eq /#.
by rewrite ec_incr_oget_in_dom_ne.
case (elem \in cnts) => [elem_in_cnts | elem_not_in_cnts].
rewrite ec_incr_oget_in_dom_eq /#.
by rewrite ec_incr_oget_not_in_dom_eq.
qed.

lemma counts_eq (cnts1 cnts2 : 'a counts) :
  dom_pos cnts1 => dom_pos cnts2 =>
  (forall (elem : 'a),
   get_count cnts1 elem = get_count cnts2 elem) =>
  cnts1 = cnts2.
proof.
move => dom_pos_cnts1 dom_pos_cnts2 get_count_eq.
apply fmap_eqP => elem.
case (elem \in cnts1) => [elem_in_cnts1 | elem_not_in_cnts1].
case (elem \in cnts2) => [elem_in_cnts2 | elem_not_in_cnts2].
have get_count_eq_elem := get_count_eq elem.
rewrite ec_get_in_dom // ec_get_in_dom // in get_count_eq_elem.
rewrite (get_some cnts1 elem) // (get_some cnts2 elem) //.
have get_count_eq_elem := get_count_eq elem.
rewrite (ec_get_in_dom cnts1 _ ) //
        (ec_get_not_in_dom cnts2 _) // in get_count_eq_elem.
have get_elem_cnts1_pos := dom_pos_cnts1 elem elem_in_cnts1.
have // : 1 <= 0 by rewrite -get_count_eq_elem.
case (elem \in cnts2) => [mem_dom2_elem | not_mem_dom2_elem].
have get_count_eq_elem := get_count_eq elem.
rewrite (ec_get_in_dom cnts2 _ ) //
        (ec_get_not_in_dom cnts1 _) // in get_count_eq_elem.
have get_elem_cnts2_pos := dom_pos_cnts2 elem mem_dom2_elem.
have // : 1 <= 0 by rewrite get_count_eq_elem.
do 2! rewrite get_none //.
qed.
