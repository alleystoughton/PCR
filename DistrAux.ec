(* DistrAux.ec *)

(* Auxiliary Lemmas on Distributions *)

prover quorum=2 ["Alt-Ergo" "Z3"].  (* both Alt-Ergo and Z3 must succeed *)

require import AllCore Distr DInterval Dexcepted Mu_mem List FSet.
require import StdRing. import RField.
require import StdOrder. import RealOrder.

lemma dinter_range_pred (n m : int) :
  n < m => mu [n .. m - 1] (fun i => n <= i < m) = 1%r.
proof.
move => lt_n_m.
have gt0_m_minus_n : 0 < m - n by rewrite -(ltz_add2r n) -addzA addNz.
have mn_eq : m - 1 + ((-n) + 1) = m - n by ring.
rewrite dinterE -addzA /= -addzA /= max_ler mn_eq
        1:ltzW 1:gt0_m_minus_n size_filter.
have [ac _] := all_count (fun (i : int) => n <= i < m) (range n m).
rewrite ac.
rewrite allP => x mem_x_ran_nm /=; by rewrite -mem_range.
by rewrite size_range max_ler 1:ltzW 1:gt0_m_minus_n -unitrE eq_fromint
   IntOrder.lt0r_neq0.
qed.

lemma dinter_in_supp_ge (i j x : int) :
  x \in [i .. j] => i <= x.
proof. rewrite /support drange1E /#. qed.

lemma dinter_in_supp_le (i j x : int) :
  x \in [i .. j] => x <= j.
proof. rewrite /support drange1E /#. qed.

lemma dinter_in_supp_le_lt (i j x : int) :
  x \in [i .. j - 1] => i <= x < j.
proof.
move => x_in_range_i_j_min1.
rewrite /support drange1E in x_in_range_i_j_min1.
smt().
qed.

lemma in_supp_minus_distr (x : 'a, d : 'a distr, p : 'a -> bool) :
  x \in (d \ p) => x \in d.
proof. by rewrite supp_dexcepted. qed.

lemma in_supp_minus_not_pred (x : 'a, d : 'a distr, p : 'a -> bool) :
  x \in (d \ p) => ! p x.
proof. by rewrite supp_dexcepted. qed.

lemma lossless_minus (d : 'a distr, n : int, xs : 'a fset) :
  0 <= n =>
  (forall (y : 'a), mu1 d y = 1%r / (2 ^ n)%r) =>
  is_lossless d =>
  card xs < 2 ^ n =>
  is_lossless (d \ mem xs).
proof.
move => ge0_n uni ll card_xs_lt_max.
rewrite dexcepted_ll 1:ll (mu_mem _ _ (1%r / (2 ^ n)%r)).
move => x mem_xs_x; apply uni.
rewrite mul1r.
have card_xs_lb_real : 0%r <= (card xs)%r
  by rewrite le_fromint fcard_ge0.
have card_xs_lt_max_real : (card xs)%r < (2 ^ n)%r
  by apply lt_fromint.
rewrite RealOrder.ltr_pdivr_mulr /#.
qed.
