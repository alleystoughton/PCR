(* Client.ec *)

(* Proof of Security Against Client *)

prover quorum=2 ["Alt-Ergo" "Z3"].  (* both Alt-Ergo and Z3 must succeed *)

(************* PCR Protocol and Supporting Definitions and Lemmas *************)

require import Protocol.

(********************************* Adversary **********************************)

(* Adversary's hashing budget *)

op adv_budget : int.

axiom adv_budget_ge0 : 0 <= adv_budget.

(* maximum number of distinct elements in database chosen by Adversary *)

op db_uniqs_max : int.

axiom db_uniqs_max_ge0 : 0 <= db_uniqs_max.

(* maximum number of queries that may be made by Adversary *)

op qrys_max : int.

axiom qrys_max_ge0 : 0 <= qrys_max.

(* total hashing budget, either performed directly by Adversary, or
   performed by Protocol due to Adversary's choices of
   database/queries *)

op budget : int = adv_budget + db_uniqs_max + qrys_max.

lemma budget_ge0 : 0 <= budget.
proof.
rewrite /budget addz_ge0 1:addz_ge0 1:adv_budget_ge0
        1:db_uniqs_max_ge0 qrys_max_ge0.
qed.

(* the following axiom implies that hash collisions aren't *forced*,
   if no more than budget hash tags are chosen *)

axiom budget_ub : budget <= 2 ^ tag_len.

(* Adversary is limited via counted random oracle *)

clone RO.Counted as CRO with
  op budget <- adv_budget
proof *.
(* beginning of realization *)
realize budget_ge0. apply adv_budget_ge0. qed.
(* end of realization *)

(* Adversary module type, parameterized by a counted random oracle *)

module type ADV(O : CRO.COR) = {
  (* all procedures are supplied the current Client view

     init_and_get_db, get_qry and qry_done may call O.chash (counted
     hashing); final may call O.hash (ordinary hashing) *)

  (* initialize Adversary, and try to get a database from it; None
     means refusal *)

  proc * init_and_get_db(cv : client_view) : db option {O.chash}

  (* try to get a query from Adversary; None means done supplying queries *)

  proc get_qry(cv : client_view) : elem option {O.chash}

  (* tell the Adversary that done processing its last query *)

  proc qry_done(cv : client_view) : unit {O.chash}

  (* finalize the Adversary, which returns its boolean judgment *)

  proc final(cv : client_view) : bool {O.hash}
}.

(*************************** Real and Ideal Games *****************************)

(* the "real" game

   parameterized by Adversary, which has counted access to random
   oracle (meaning it may do unlimited hashing, but it's monitored for
   whether it stays within budget) *)

module GReal(Adv : ADV) : GAME = {
  module Or  = RO.Or        (* random oracle *)
  module COr = CRO.COr(Or)  (* counted random oracle built from Or *)
  module A   = Adv(COr)     (* specialization of Adversary to COr *)

  (* custom environment to be passed to Protocol *)

  module Env : ENV = {
    var qrys_ctr : int  (* number of queries processed *)

    proc init_and_get_db() : db option = {
      var db_opt : db option; var adv_within_budg : bool;
      qrys_ctr <- 0;
      COr.init();  (* Or.init is called by Protocol.main *)
      db_opt <@ A.init_and_get_db(Protocol.cv);
      if (db_opt <> None) {
        (* if too many elements in oget db_opt or Adversary has
           already exceeded its hashing budget, return None *)
        adv_within_budg <@ COr.within_budget();
        if (db_uniqs_max < num_uniqs(oget db_opt) \/ !adv_within_budg) {
          db_opt <- None;
        }
      }
      return db_opt;
    }

    proc get_qry() : elem option = {
      var qry_opt : elem option;
      var adv_within_budg : bool;
      qry_opt <@ A.get_qry(Protocol.cv);
      if (qry_opt <> None) {
        (* if too many queries have been processed or Adversary has
           exceeded its hashing budget, return None; otherwise note
           that one more query has been processed *)
        adv_within_budg <@ COr.within_budget();
        if (qrys_ctr < qrys_max /\ adv_within_budg) {
          qrys_ctr <- qrys_ctr + 1;
        }
        else {
          qry_opt <- None;
        }
      }
      return qry_opt;
    }

    proc put_qry_count(cnt : int) : unit = {
      (* ignore the count, but Protocol.cv contains
         it *)
      A.qry_done(Protocol.cv);
    }

    proc final() : bool = {
      var b : bool;
      b <@ A.final(Protocol.cv);
      return b;
    }
  }

  proc main() : bool = {
    var b : bool;
    b <@ Protocol(Env).main();
    return b;
  }
}.

(* Client's Simulator's interface to Ideal Game *)

module type SIG = {
  (* ask Ideal Game for next query along with its count; None means no
     more queries

     this involves the Ideal Game communicating with Adversary *)

  proc get_qry_count(cv : client_view) : (elem * int) option

  (* say that done processing a query *)

  proc qry_done(cv : client_view) : unit
}.

(* module type for Client's Simulator

   parameterized by random oracle and Simulator's interface to Ideal
   Game, SIG

   only client_loop may call procedures of SIG or O (Simulator can't
   directly use RO.Or because of module restriction in top-level
   theorem) *)

module type SIM(O : RO.OR, SIG : SIG) = {
  (* initialization *)

  proc * init() : unit { (* no use of O, SIG *) }

  (* get current view *)

  proc get_view() : client_view { (* no use of O, SIG *) }

  (* run the Client's query loop *)

  proc client_loop() : unit {O.hash SIG.get_qry_count SIG.qry_done}
}.

(* the "ideal" game

   parameterized by Adversary and Simulator for Client

   database is turned into elements counts map, which is used for
   processing Simulator's queries *)

module GIdeal (Adv : ADV, Sim : SIM) : GAME = {
  module Or  = RO.Or        (* random oracle *)
  module COr = CRO.COr(Or)  (* counted random oracle built from Or *)
  module A   = Adv(COr)     (* specialization of Adversary to COr *)

  var db_elems_cnts : elems_counts  (* elements counts map for database *)
  var qrys_ctr : int                (* number queries processed *)

  (* turn database into elements counts map *)

  proc count_db(db : db) : unit = {
    var i : int; var elem : elem;
    db_elems_cnts <- empty_ec; i <- 0;
    while (i < size db) {
      elem <- nth elem_default db i;
      db_elems_cnts <- incr_count db_elems_cnts elem;
      i <- i + 1;
    }
  }

  (* Simulator's interface to Ideal Game *)

  module SIG : SIG = {
    proc get_qry_count(cv : client_view) : (elem * int) option = {
      var qry_opt : elem option;
      var qry_cnt_opt : (elem * int) option;
      var adv_within_budg : bool; var cnt : int;
      qry_opt <@ A.get_qry(cv);
      if (qry_opt = None) {
        qry_cnt_opt <- None;
      }
      else {
        (* has Adversary proposed too many queries or exceeded its
           hashing budget? *)
        adv_within_budg <@ COr.within_budget();
        if (qrys_ctr < qrys_max /\ adv_within_budg) {
          qrys_ctr <- qrys_ctr + 1;
          cnt <- get_count db_elems_cnts (oget qry_opt);
          qry_cnt_opt <- Some (oget qry_opt, cnt);
        }
        else {
          qry_cnt_opt <- None;
        }
      }
      return qry_cnt_opt;
    }

    proc qry_done(cv : client_view) : unit = {
      A.qry_done(cv);
    }
  }

  (* connect Simulator with Or and SIG *)
  module S = Sim(Or, SIG)

  proc main() : bool = {
    var db_opt : db option; var b : bool; var adv_within_budg : bool;
    var cv : client_view;
    qrys_ctr <- 0; S.init();
    Or.init(); COr.init();
    cv <@ S.get_view(); db_opt <@ A.init_and_get_db(cv);
    if (db_opt <> None) {
      (* if too many elements in oget db_opt or Adversary has already
         exceeded its hashing budget, then skip main part of game *)
      adv_within_budg <@ COr.within_budget();
      if (num_uniqs(oget db_opt) <= db_uniqs_max /\ adv_within_budg) {
        (* turn oget db_opt into elements counts map, db_elems_cnts;
           nothing else is done with oget db_opt *)
        count_db(oget db_opt);
        S.client_loop();  (* run the Simulator's client loop *)
      }
    }
    cv <@ S.get_view(); b <@ A.final(cv);
    return b;
  }
}.

(* see end-of-file for top-level theorem *)

(********************************* Proof Body *********************************)

(* Client's Simulator *)

module (Sim : SIM) (O : RO.OR, SIG : SIG) = {
  var cv : client_view
  var sec : sec

  proc init() : unit = {
    sec <$ sec_distr;
    cv <- [cv_got_sec sec];
  }

  proc get_view() : client_view = {
    return cv;
  }

  proc client_loop() : unit = {
    var tag : tag; var qry : elem; var cnt : int;
    var qry_cnt_opt : (elem * int) option;
    var not_done : bool <- true;
    while (not_done) {
      qry_cnt_opt <@ SIG.get_qry_count(cv);
      if (qry_cnt_opt = None) {
        not_done <- false;
        cv <- cv ++ [cv_got_qry None];
      }
      else {
        (qry, cnt) <- oget qry_cnt_opt;
        cv <- cv ++ [cv_got_qry (Some qry)];
        tag <@ O.hash((qry, sec));
        cv <- cv ++ [cv_query_count(qry, tag, cnt)];
        SIG.qry_done(cv);
      }
    }
  }
}.

(************************* Theories Supporting Proof **************************)

(* injective maps *)

require import Inj.

(* numbers of occurrences of elements in lists *)

require import NumOccs.

(* iteration over lists *)

require IterProc.  (* abstract theory *)

(******************************** Proof Section *******************************)

(* the rest of the proof is within a section, in which the Adversary,
   Adv, is declared locally *)

section.

(* declare Adversary module -- subsequent games will reference it, instead
   of being parameterized by it *)

declare module Adv <: ADV{GReal, GIdeal, Sim}.

(* these axioms will be preconditions of the lemma we export
   from section *)

declare axiom init_and_get_db_ll :
  forall (O <: CRO.COR{Adv}),
  islossless O.chash => islossless Adv(O).init_and_get_db.

declare axiom get_qry_ll :
  forall (O <: CRO.COR{Adv}),
  islossless O.chash => islossless Adv(O).get_qry.

declare axiom qry_done_ll :
  forall (O <: CRO.COR{Adv}),
  islossless O.chash => islossless Adv(O).qry_done.

declare axiom final_ll :
  forall (O <: CRO.COR{Adv}),
  islossless O.hash => islossless Adv(O).final.

(* budgeted random oracle *)

local clone RO.BudgetedRandomOracle as BRO with
  op adv_budget <- adv_budget,
  op serv_budget <- db_uniqs_max,
  op clnt_budget <- qrys_max
proof *.
(* beginning of realization *)
realize adv_budget_ge0. apply adv_budget_ge0. qed.

realize serv_budget_ge0. apply db_uniqs_max_ge0. qed.

realize clnt_budget_ge0. apply qrys_max_ge0. qed.

realize sum_budgets_ub. rewrite -/budget budget_ub. qed.
(* end of realization *)

local lemma Or_hash_BOr_server_bhash :
  equiv
  [RO.Or.hash ~ BRO.BOr.server_bhash :
   ={inp} /\ RO.Or.mp{1} = BRO.BOr.mp{2} ==>
   ={res} /\ RO.Or.mp{1} = BRO.BOr.mp{2}].
proof.
proc; inline BRO.BOr.hash.
if{2}; wp; sim.
qed.

local lemma Or_hash_BOr_client_bhash :
  equiv
  [RO.Or.hash ~ BRO.BOr.client_bhash :
   ={inp} /\ RO.Or.mp{1} = BRO.BOr.mp{2} ==>
   ={res} /\ RO.Or.mp{1} = BRO.BOr.mp{2}].
proof.
proc; inline BRO.BOr.hash.
if{2}; wp; sim.
qed.

(* convert a budgeted random oracle to a counted random oracle
   for giving to Adversary

   only chash and hash will be used *)

local module BOrToCOr(O : BRO.BOR) : CRO.COR = {
  proc chash(inp : elem * sec) : tag = {
    var out : tag;
    out <@ O.adv_bhash(inp);
    return out;
  }

  proc hash = O.hash

  proc init() : unit = {}  (* dummy *)

  proc within_budget() : bool = {  (* dummy *)
    return false;
  }
}.

local lemma COr_Or_chash_BOr_adv_bhash :
  equiv
  [CRO.COr(RO.Or).chash ~ BRO.BOr.adv_bhash :
   ={inp} /\
   RO.Or.mp{1} = BRO.BOr.mp{2} /\
   CRO.COr.inps{1} = BRO.BOr.adv_inps{2} /\
   CRO.COr.ctr{1} = BRO.BOr.adv_ctr{2} /\
   CRO.COr.over{1} = BRO.BOr.adv_over{2} ==>
   ={res} /\
   RO.Or.mp{1} = BRO.BOr.mp{2} /\
   CRO.COr.inps{1} = BRO.BOr.adv_inps{2} /\
   CRO.COr.ctr{1} = BRO.BOr.adv_ctr{2} /\
   CRO.COr.over{1} = BRO.BOr.adv_over{2}].
proof. sim. qed.

local lemma COr_Or_BOrToCOr_BOr_chash :
  equiv
  [CRO.COr(RO.Or).chash ~ BOrToCOr(BRO.BOr).chash :
   ={inp} /\
   RO.Or.mp{1} = BRO.BOr.mp{2} /\
   CRO.COr.inps{1} = BRO.BOr.adv_inps{2} /\
   CRO.COr.ctr{1} = BRO.BOr.adv_ctr{2} /\
   CRO.COr.over{1} = BRO.BOr.adv_over{2} ==>
   ={res} /\
   RO.Or.mp{1} = BRO.BOr.mp{2} /\
   CRO.COr.inps{1} = BRO.BOr.adv_inps{2} /\
   CRO.COr.ctr{1} = BRO.BOr.adv_ctr{2} /\
   CRO.COr.over{1} = BRO.BOr.adv_over{2}].
proof.
proc*; inline BOrToCOr(BRO.BOr).chash; wp.
call COr_Or_chash_BOr_adv_bhash.
auto.
qed.

local lemma COr_Or_BOrToCOr_BOr_hash :
  equiv
  [CRO.COr(RO.Or).hash ~ BOrToCOr(BRO.BOr).hash :
   ={inp} /\ RO.Or.mp{1} = BRO.BOr.mp{2} ==>
   ={res} /\ RO.Or.mp{1} = BRO.BOr.mp{2}].
proof. sim. qed.

(* H1 is like GReal(Adv), except

   - it takes a budgeted random oracle O as its parameter

   - Adversary is given result of converting O to counted random
     oracle, Server uses O.server_bhash, Client uses O.client_bhash,
     and O.adv_within_budget is used to check if Adversary is
     within budget

   - inlining and dead code elimination have been done *)

local module H1(O : BRO.BOR) = {
  module A = Adv(BOrToCOr(O))

  var cv : client_view
  var sec : sec
  var hdb : hdb
  var qrys_ctr : int

  proc server_hash_db(db : db) : unit = {
    var i : int; var elem : elem; var tag : tag;
    db <- Shuffle.shuffle(db);
    hdb <- []; i <- 0;
    while (i < size db) {
      elem <- nth elem_default db i;
      tag <@ O.server_bhash((elem, sec));
      hdb <- hdb ++ [tag];
      i <- i + 1;
    }
  }

  proc tp_count_tag(tag : tag) : int = {
    var i, cnt : int;
    cnt <- 0; i <- 0;
    while (i < size hdb) {
      if (nth zeros_tag hdb i = tag) {
        cnt <- cnt + 1;
      }
      i <- i + 1;
    }
    return cnt;
  }

  proc client_loop() : unit = {
    var cnt : int;
    var tag : tag;
    var qry_opt : elem option;
    var not_done : bool <- true;
    var adv_within_budg : bool;
    while (not_done) {
      qry_opt <@ A.get_qry(cv);
      if (qry_opt = None) {
        not_done <- false;
        cv <- cv ++ [cv_got_qry None];
      }
      else {
        adv_within_budg <@ O.adv_within_budget();
        if (qrys_ctr < qrys_max /\ adv_within_budg) {
          cv <- cv ++ [cv_got_qry qry_opt];
          qrys_ctr <- qrys_ctr + 1;
          tag <@ O.client_bhash((oget qry_opt, sec));
          cnt <@ tp_count_tag(tag);
          cv <- cv ++ [cv_query_count(oget qry_opt, tag, cnt)];
          A.qry_done(cv);
        }
        else {
          not_done <- false;
          cv <- cv ++ [cv_got_qry None];
        }
      }
    }
  }

  proc main() : bool = {
    var db_opt : db option;
    var b : bool;
    var adv_within_budg : bool;
    sec <$ sec_distr;
    cv <- [cv_got_sec sec];
    qrys_ctr <- 0;
    O.init();
    db_opt <@ A.init_and_get_db(cv);
    if (db_opt <> None) {
      adv_within_budg <@ O.adv_within_budget();
      if (num_uniqs(oget db_opt) <= db_uniqs_max /\ adv_within_budg) {
        server_hash_db(oget db_opt);
        client_loop();
      }
    }
    b <@ A.final(cv);
    return b;
  }
}.

(* G1 is identical to H1 except it uses oracle BRO.BOr, instead of
   being parameterized by budgeted random oracle *)

local module G1 = H1(BRO.BOr).

local lemma Protocol_GReal_Env_G1_server_hash_db :
  equiv
  [Protocol(GReal(Adv).Env).server_hash_db ~ G1.server_hash_db :
   ={db} /\ ={mp}(RO.Or, BRO.BOr) /\ Protocol.server_sec{1} = G1.sec{2} ==>
   Protocol.server_hdb{1} = G1.hdb{2} /\ ={mp}(RO.Or, BRO.BOr)].
proof.
sim
  (: ={mp}(RO.Or, BRO.BOr)) / true :
  (Protocol.server_hdb{1} = G1.hdb{2} /\ ={mp}(RO.Or, BRO.BOr)).
apply Or_hash_BOr_server_bhash.
qed.

local lemma Protocol_GReal_Env_G1_client_loop :
  equiv
  [Protocol(GReal(Adv).Env).client_loop ~ G1.client_loop :
   ={glob Adv} /\ RO.Or.mp{1} = BRO.BOr.mp{2} /\
   CRO.COr.inps{1} = BRO.BOr.adv_inps{2} /\
   CRO.COr.ctr{1} = BRO.BOr.adv_ctr{2} /\
   CRO.COr.over{1} = BRO.BOr.adv_over{2} /\
   Protocol.client_sec{1} = G1.sec{2} /\
   GReal.Env.qrys_ctr{1} = G1.qrys_ctr{2} /\
   Protocol.tp_hdb{1} = G1.hdb{2} /\ Protocol.cv{1} = G1.cv{2} ==>
   ={glob Adv} /\ RO.Or.mp{1} = BRO.BOr.mp{2} /\
   CRO.COr.inps{1} = BRO.BOr.adv_inps{2} /\
   CRO.COr.ctr{1} = BRO.BOr.adv_ctr{2} /\
   CRO.COr.over{1} = BRO.BOr.adv_over{2} /\
   GReal.Env.qrys_ctr{1} = G1.qrys_ctr{2} /\ Protocol.cv{1} = G1.cv{2}].
proof.
proc.
inline GReal(Adv).Env.get_qry GReal(Adv).Env.put_qry_count.
sp.
while
  (={not_done, glob Adv} /\ RO.Or.mp{1} = BRO.BOr.mp{2} /\
   CRO.COr.inps{1} = BRO.BOr.adv_inps{2} /\
   CRO.COr.ctr{1} = BRO.BOr.adv_ctr{2} /\
   CRO.COr.over{1} = BRO.BOr.adv_over{2} /\
   Protocol.client_sec{1} = G1.sec{2} /\
   GReal.Env.qrys_ctr{1} = G1.qrys_ctr{2} /\
  Protocol.tp_hdb{1} = G1.hdb{2} /\ Protocol.cv{1} = G1.cv{2}).
seq 1 1 :
  (={not_done, glob Adv} /\ RO.Or.mp{1} = BRO.BOr.mp{2} /\
   CRO.COr.inps{1} = BRO.BOr.adv_inps{2} /\
   CRO.COr.ctr{1} = BRO.BOr.adv_ctr{2} /\
   CRO.COr.over{1} = BRO.BOr.adv_over{2} /\
   Protocol.client_sec{1} = G1.sec{2} /\
   GReal.Env.qrys_ctr{1} = G1.qrys_ctr{2} /\
   Protocol.tp_hdb{1} = G1.hdb{2} /\ Protocol.cv{1} = G1.cv{2} /\
   qry_opt0{1} = qry_opt{2}).
call
  (_ :
   RO.Or.mp{1} = BRO.BOr.mp{2} /\
   CRO.COr.inps{1} = BRO.BOr.adv_inps{2} /\
   CRO.COr.ctr{1} = BRO.BOr.adv_ctr{2} /\
   CRO.COr.over{1} = BRO.BOr.adv_over{2}).
apply COr_Or_BOrToCOr_BOr_chash.
auto.
case (qry_opt{2} = None).
rcondf{1} 1; first auto. rcondt{2} 1; first auto.
rcondt{1} 3; first auto.
auto.
rcondt{1} 1; first auto. rcondf{2} 1; first auto.
inline GReal(Adv).COr.within_budget BRO.BOr.adv_within_budget.
sp 1 1.
if => //.
rcondf{1} 4; first auto.
call
  (_ :
   RO.Or.mp{1} = BRO.BOr.mp{2} /\
   CRO.COr.inps{1} = BRO.BOr.adv_inps{2} /\
   CRO.COr.ctr{1} = BRO.BOr.adv_ctr{2} /\
   CRO.COr.over{1} = BRO.BOr.adv_over{2}).
apply COr_Or_BOrToCOr_BOr_chash.
wp.
call (_ : Protocol.tp_hdb{1} = G1.hdb{2}); first sim.
call Or_hash_BOr_client_bhash.
auto.
rcondt{1} 4; first auto.
auto.
auto.
qed.

local lemma GReal_G1_main :
  equiv[GReal(Adv).main ~ G1.main : true ==> ={res}].
proof.
proc.
inline Protocol(GReal(Adv).Env).main
       Protocol(GReal(Adv).Env).init_views
       Protocol(GReal(Adv).Env).server_gen_sec
       Protocol(GReal(Adv).Env).client_receive_sec
       Protocol(GReal(Adv).Env).tp_receive_hdb
       Protocol(GReal(Adv).Env).server_get_hdb
       Protocol(GReal(Adv).Env).server_get_sec
       GReal(Adv).Env.init_and_get_db
       GReal(Adv).Env.final.
seq 11 4 :
  (RO.Or.mp{1} = BRO.BOr.mp{2} /\
   CRO.COr.inps{1} = BRO.BOr.adv_inps{2} /\
   CRO.COr.ctr{1} = BRO.BOr.adv_ctr{2} /\
   CRO.COr.over{1} = BRO.BOr.adv_over{2} /\
   Protocol.server_sec{1} = G1.sec{2} /\
   GReal.Env.qrys_ctr{1} = G1.qrys_ctr{2} /\
   Protocol.client_sec{1} = G1.sec{2} /\
   Protocol.cv{1} = G1.cv{2}).
swap{1} 5 -4; inline *; auto.
seq 1 1 :
  (={glob Adv} /\
   RO.Or.mp{1} = BRO.BOr.mp{2} /\
   CRO.COr.inps{1} = BRO.BOr.adv_inps{2} /\
   CRO.COr.ctr{1} = BRO.BOr.adv_ctr{2} /\
   CRO.COr.over{1} = BRO.BOr.adv_over{2} /\
   Protocol.server_sec{1} = G1.sec{2} /\
   GReal.Env.qrys_ctr{1} = G1.qrys_ctr{2} /\
   Protocol.client_sec{1} = G1.sec{2} /\
   Protocol.cv{1} = G1.cv{2} /\ db_opt0{1} = db_opt{2}).
call
  (_ :
   RO.Or.mp{1} = BRO.BOr.mp{2} /\
   CRO.COr.inps{1} = BRO.BOr.adv_inps{2} /\
   CRO.COr.ctr{1} = BRO.BOr.adv_ctr{2} /\
   CRO.COr.over{1} = BRO.BOr.adv_over{2}).
apply COr_Or_BOrToCOr_BOr_chash.
auto.
if => //.
inline GReal(Adv).COr.within_budget BRO.BOr.adv_within_budget.
sp 1 1; wp.
case
  (num_uniqs (oget db_opt{2}) <= db_uniqs_max /\
   adv_within_budg{2}).
rcondf{1} 1; first auto; smt().
rcondt{2} 1; first auto.
rcondt{1} 2; first auto.
call (_ : RO.Or.mp{1} = BRO.BOr.mp{2}).
apply COr_Or_BOrToCOr_BOr_hash.
call Protocol_GReal_Env_G1_client_loop.
wp.
call Protocol_GReal_Env_G1_server_hash_db; auto.
rcondt{1} 1; first auto; smt().
rcondf{2} 1; first auto.
rcondf{1} 3; first auto.
call (_ : RO.Or.mp{1} = BRO.BOr.mp{2}).
apply COr_Or_BOrToCOr_BOr_hash.
auto.
rcondf{1} 2; first auto.
wp.
call (_ : RO.Or.mp{1} = BRO.BOr.mp{2}).
apply COr_Or_BOrToCOr_BOr_hash.
auto.
qed.

local lemma GReal_G1 &m :
  Pr[GReal(Adv).main() @ &m : res] = Pr[G1.main() @ &m : res].
proof. by byequiv GReal_G1_main. qed.

(* G2 is the same as G1, except it uses BRO.BOrInj (which will stay
   collision free (injective) as long as all three budgets are
   respected and only budgeted hashing is done) not BRO.BOr *)

local module G2 = H1(BRO.BOrInj).

(* we apply the Switching lemma to G1/G2

   our concrete switching adversary H1' is the same as H1, except that
   its main procedure doesn't (can't!) initialize the oracle, and hdb
   is initialized by main *)

local module (H1' : BRO.SWADV) (O : BRO.BOR) = {
  module A = Adv(BOrToCOr(O))

  var cv : client_view
  var sec : sec
  var hdb : hdb
  var qrys_ctr : int

  proc server_hash_db(db : db) : unit = {
    var i : int;
    var elem : elem;
    var tag : tag;
    db <- Shuffle.shuffle(db);
    hdb <- []; i <- 0;
    while (i < size db) {
      elem <- nth elem_default db i;
      tag <@ O.server_bhash((elem, sec));
      hdb <- hdb ++ [tag];
      i <- i + 1;
    }
  }

  proc tp_count_tag(tag : tag) : int = {
    var i, cnt : int;
    cnt <- 0; i <- 0;
    while (i < size hdb) {
      if (nth zeros_tag hdb i = tag) {
        cnt <- cnt + 1;
      }
      i <- i + 1;
    }
    return cnt;
  }

  proc client_loop() : unit = {
    var cnt : int;
    var tag : tag;
    var qry_opt : elem option;
    var not_done : bool <- true;
    var adv_within_budg : bool;
    while (not_done) {
      qry_opt <@ A.get_qry(cv);
      if (qry_opt = None) {
        not_done <- false;
        cv <- cv ++ [cv_got_qry None];
      }
      else {
        adv_within_budg <@ O.adv_within_budget();
        if (qrys_ctr < qrys_max /\ adv_within_budg) {
          cv <- cv ++ [cv_got_qry qry_opt];
          qrys_ctr <- qrys_ctr + 1;
          tag <@ O.client_bhash((oget qry_opt, sec));
          cnt <@ tp_count_tag(tag);
          cv <- cv ++ [cv_query_count(oget qry_opt, tag, cnt)];
          A.qry_done(cv);
        }
        else {
          not_done <- false;
          cv <- cv ++ [cv_got_qry None];
        }
      }
    }
  }

  proc main() : bool = {
    var db_opt : db option;
    var b : bool;
    var adv_within_budg : bool;
    sec <$ sec_distr;
    cv <- [cv_got_sec sec];
    qrys_ctr <- 0;
    hdb <- [];
    db_opt <@ A.init_and_get_db(cv);
    if (db_opt <> None) {
      adv_within_budg <@ O.adv_within_budget();
      if (num_uniqs (oget db_opt) <= db_uniqs_max /\ adv_within_budg) {
        server_hash_db(oget db_opt);
        client_loop();
      }
    }
    b <@ A.final(cv);
    return b;
  }
}.

(* we work up to showing losslessness of H1'.main *)

local lemma H1'_server_hash_db_ll :
  forall (O <: BRO.BOR),
  islossless O.server_bhash => islossless H1'(O).server_hash_db.
proof.
move => O server_bhash_ll; proc.
while (true) (size db - i).
move => z; wp.
call (_ : true ==> true).
auto; smt().
wp.
call (_ : true ==> true); first apply Shuffle_shuffle_ll.
auto; smt().
qed.

local lemma H1'_tp_count_tag_ll :
  forall (O <: BRO.BOR),
  islossless H1'(O).tp_count_tag.
proof.
move => O; proc; wp.
while (true) (size H1'.hdb - i).
auto; smt().
auto; smt().
qed.

local lemma H1'_client_loop_ll :
  forall (O <: BRO.BOR{H1'}),
  islossless O.adv_bhash => islossless O.adv_within_budget =>
  islossless O.server_bhash => islossless O.client_bhash =>
  islossless O.hash =>
  phoare
  [H1'(O).client_loop :
   H1'.qrys_ctr <= qrys_max ==> true] = 1%r.
proof.
move =>
  O adv_bhash_ll adv_within_budget_ll server_bhash_ll
  client_bhash_ll hash_ll.
proc; sp.
while (H1'.qrys_ctr <= qrys_max)
      (b2i not_done * (qrys_max - H1'.qrys_ctr + 1)).
auto.
seq 1 :
  (H1'.qrys_ctr <= qrys_max /\ not_done /\
   b2i not_done * (qrys_max - H1'.qrys_ctr + 1) = z).
auto.
call (_ : true ==> true).
apply (get_qry_ll (BOrToCOr(O))); proc; call adv_bhash_ll; auto.
auto.
if.
auto; smt().
seq 1 :
  (H1'.qrys_ctr <= qrys_max /\ not_done /\
   b2i not_done * (qrys_max - H1'.qrys_ctr + 1) = z).
call (_ : true); first auto.
call adv_within_budget_ll; auto.
if.
call (_ : true ==> true).
apply (qry_done_ll (BOrToCOr(O))); proc; call adv_bhash_ll; auto.
wp.
call (H1'_tp_count_tag_ll O).
call client_bhash_ll.
auto; smt().
auto; smt().
hoare.
call (_ : true); auto; smt().
smt().
hoare.
call (_ : true); auto; smt().
smt().
auto; smt().
qed.

local lemma H1'_main_ll :
  forall (O <: BRO.BOR{H1'}),
  islossless O.adv_bhash => islossless O.adv_within_budget =>
  islossless O.server_bhash => islossless O.client_bhash =>
  islossless O.hash =>
  islossless H1'(O).main.
proof.
move =>
  O adv_bhash_ll adv_within_budget_ll server_bhash_ll client_bhash_ll
  hash_ll.
proc.
call (_ : true ==> true).
apply (final_ll (BOrToCOr(O))); apply hash_ll.
seq 5 : (H1'.qrys_ctr = 0).
call (_ : true).
proc; call (_ : true); auto.
auto.
call (_ : true ==> true).
apply (init_and_get_db_ll (BOrToCOr(O))); proc; call adv_bhash_ll; auto.
auto; progress; apply sec_distr_ll.
if.
seq 1 : (H1'.qrys_ctr = 0 /\ db_opt <> None).
call (_ : true); auto.
call adv_within_budget_ll; auto.
if.
call (_ : H1'.qrys_ctr <= qrys_max ==> true).
apply (H1'_client_loop_ll O);
  [apply adv_bhash_ll | apply adv_within_budget_ll |
   apply server_bhash_ll | apply client_bhash_ll |
   apply hash_ll].
call (_ : true ==> true).
apply (H1'_server_hash_db_ll O); apply server_bhash_ll.
auto; progress; apply qrys_max_ge0.
auto.
hoare; call (_ : true); auto.
trivial.
auto.
hoare.
call (_ : true).
proc; call (_ : true); auto.
auto.
trivial.
qed.

(* now we apply the Switching Lemma to H1' *)

local lemma GSwitching_H1' &m :
  `|Pr[BRO.GSwitching(H1', BRO.BOr).main() @ &m : res] -
    Pr[BRO.GSwitching(H1', BRO.BOrInj).main() @ &m : res]| <=
  BRO.coll_bound.
proof.
apply (BRO.Switching H1' &m).
move => O; apply (H1'_main_ll O).
qed.

(* now we connect G1 and G2 *)

local lemma G1_GSwitching_H1'_BOr_main &m :
  equiv
  [G1.main ~ BRO.GSwitching(H1', BRO.BOr).main :
   true ==> ={res}].
proof.
proc.
inline BRO.GSwitching(H1', BRO.BOr).SA.main.
swap{1} 4 -3; sim.
qed.

local lemma G1_GSwitching_H1'_BOr &m :
  Pr[G1.main() @ &m : res] =
  Pr[BRO.GSwitching(H1', BRO.BOr).main() @ &m : res].
proof. by byequiv (G1_GSwitching_H1'_BOr_main &m). qed.

local lemma GSwitching_H1'_BOrInj_G2_main &m :
  equiv
  [BRO.GSwitching(H1', BRO.BOrInj).main ~ G2.main:
   true ==> ={res}].
proof.
proc.
inline BRO.GSwitching(H1', BRO.BOrInj).SA.main.
swap{2} 4 -3; sim.
qed.

local lemma GSwitching_H1'_BOrInj_G2 &m :
  Pr[BRO.GSwitching(H1', BRO.BOrInj).main() @ &m : res] =
  Pr[G2.main() @ &m : res].
proof. by byequiv (GSwitching_H1'_BOrInj_G2_main &m). qed.

local lemma G1_G2 &m :
  `|Pr[G1.main() @ &m : res] - Pr[G2.main() @ &m : res]| <=
  BRO.coll_bound.
proof.
rewrite (G1_GSwitching_H1'_BOr &m) -(GSwitching_H1'_BOrInj_G2 &m)
        (GSwitching_H1' &m).
qed.

local lemma GReal_G2 &m :
  `|Pr[GReal(Adv).main() @ &m : res] - Pr[G2.main() @ &m : res]| <=
   BRO.coll_bound.
proof. rewrite (GReal_G1 &m) (G1_G2 &m). qed.

(* In H2:

   server_hash_db is renamed to server_hash_and_count_db; it still
   hashes the database, but no longer constructs the hashed database
   (and thus the global variable hdb is deleted) -- instead it
   produces an elements counts map from the database

   client_loop now asks the TP to look up the counts for a query
   in the elements counts map, but it still hashes each query *)

local module H2(O : BRO.BOR) = {
  module A = Adv(BOrToCOr(O))

  var cv : client_view
  var sec : sec
  var elems_cnts : elems_counts
  var qrys_ctr : int

  proc server_count_and_hash_db(db : db) : unit = {
    var i : int; var elem : elem; var tag : tag;
    db <- Shuffle.shuffle(db);
    elems_cnts <- empty_ec; i <- 0;
    while (i < size db) {
      elem <- nth elem_default db i;
      elems_cnts <- incr_count elems_cnts elem;
      tag <@ O.server_bhash((elem, sec));
      i <- i + 1;
    }
  }

  proc tp_count_elem(attr : elem) : int = {
    return get_count elems_cnts attr;
  }

  proc client_loop() : unit = {
    var cnt : int; var tag : tag; var qry_opt : elem option;
    var not_done : bool <- true;
    var adv_within_budg : bool;
    while (not_done) {
      qry_opt <@ A.get_qry(cv);
      if (qry_opt = None) {
        not_done <- false;
        cv <- cv ++ [cv_got_qry None];
      }
      else {
        adv_within_budg <@ O.adv_within_budget();
        if (qrys_ctr < qrys_max /\ adv_within_budg) {
          cv <- cv ++ [cv_got_qry qry_opt];
          qrys_ctr <- qrys_ctr + 1;
          tag <@ O.client_bhash((oget qry_opt, sec));
          cnt <@ tp_count_elem(oget qry_opt);
          cv <- cv ++ [cv_query_count(oget qry_opt, tag, cnt)];
          A.qry_done(cv);
        }
        else {
          not_done <- false;
          cv <- cv ++ [cv_got_qry None];
        }
      }
    }
  }

  proc main() : bool = {
    var db_opt : db option;
    var b : bool;
    var adv_within_budg : bool;
    sec <$ sec_distr;
    cv <- [cv_got_sec sec];
    qrys_ctr <- 0;
    O.init();
    db_opt <@ A.init_and_get_db(cv);
    if (db_opt <> None) {
      adv_within_budg <@ O.adv_within_budget();
      if (num_uniqs (oget db_opt) <= db_uniqs_max /\ adv_within_budg) {
        server_count_and_hash_db(oget db_opt);
        client_loop();
      }
    }
    b <@ A.final(cv);
    return b;
  }
}.

(* G3 is like H2 except it uses oracle BRO.BOrInj, instead of being
   parameterized by an oracle *)

local module G3 = H2(BRO.BOrInj).

(* to prove G2 equivalent to G3, we need an invariant relating
   the secret, hashed database (in G2), oracle's map, and elements
   counts map (in G3)

   see NumOccs.ec for the definition of num_occs, and
   see Inj.ec for injectivity predicate, inj *)

pred counting
     (sec : sec, hdb : hdb, mp : (elem * sec, tag) fmap,
      elems_cnts : elems_counts) =
  (forall (tag : tag),
   mem hdb tag => rng mp tag) /\
  (forall (elem : elem),
   ! dom elems_cnts elem =>
   ! dom mp (elem, sec) \/
   num_occs (oget mp.[(elem, sec)]) hdb = 0) /\
  (forall (elem : elem),
   dom elems_cnts elem =>
   dom mp (elem, sec) /\
   num_occs (oget mp.[(elem, sec)]) hdb = oget elems_cnts.[elem]).

lemma counting_num_occs_get_count
  (sec : sec, hdb : hdb, mp : (elem * sec, tag) fmap,
   elems_cnts : elems_counts, elem : elem, tag : tag) :
  counting sec hdb mp elems_cnts =>
  mp.[(elem, sec)] = Some tag =>
  num_occs tag hdb = get_count elems_cnts elem.
proof.
move => [_ [ctg2 ctg3]] lu_mp_elem_sec_tag.
have in_dom_mp_elem_sec : dom mp (elem, sec)
  by rewrite domE lu_mp_elem_sec_tag.
have oget_mp_elem_seq_tag : oget mp.[(elem, sec)] = tag
  by rewrite lu_mp_elem_sec_tag.
smt().
qed.

lemma counting_in_ec_dom_impl_in_dom_or
  (sec : sec, hdb : hdb, mp : (elem * sec, tag) fmap,
   elems_cnts : elems_counts, elem : elem) :
  counting sec hdb mp elems_cnts => dom elems_cnts elem =>
  dom mp (elem, sec).
proof.
move => [_ [_ ctg3]] mem_dom_ec_elem.
have // := ctg3 elem mem_dom_ec_elem.
qed.

lemma counting_empty (sec : sec, mp : (elem * sec, tag) fmap) :
  counting sec [] mp empty_ec.
proof.
split; first smt(in_nil).
split; first smt(num_occs_nil).
smt(mem_empty).
qed.

lemma counting_add_or_new_sec
  (sec : sec, hdb : hdb, mp : (elem * sec, tag) fmap, elems_cnts : elems_counts,
   elem : elem, tag : tag) :
  counting sec hdb mp elems_cnts =>
  ! dom mp (elem, sec) => ! rng mp tag =>
  counting sec hdb (mp.[(elem, sec) <- tag]) elems_cnts.
proof.
move => ctg mem_dom_mp_elem_sec not_mem_rng_mp_tag.
split => [tag' mem_hdb_tag' |].
rewrite -mem_frng frng_set in_fsetU1 rem_id // mem_frng; smt().
split => [elem' not_mem_dom_ec_elem' | elem' mem_dom_ec_elem'].
case (elem' = elem) => [<<- | ne_elem'_elem].
right.
rewrite get_set_sameE num_occs_not_mem_imp0 /#.
have [not_mem_dom_mp_elem'_sec | num_occs_get_mp_elem'_sec_hdb_eq0] :
  ! dom mp (elem', sec) \/
  num_occs (oget mp.[(elem', sec)]) hdb = 0 by smt().
left; rewrite mem_set /#.
right.
by rewrite get_setE /= ne_elem'_elem /= num_occs_not_mem_imp0
           1:num_occs_zero_imp_notmem.
rewrite mem_set get_setE; smt().
qed.

lemma counting_add_or_new_non_sec
  (sec : sec, hdb : hdb, mp : (elem * sec, tag) fmap,
   elems_cnts : elems_counts, elem : elem, sec' : sec, tag : tag) :
  counting sec hdb mp elems_cnts =>
  sec' <> sec => ! dom mp (elem, sec') =>
  counting sec hdb (mp.[(elem, sec') <- tag]) elems_cnts.
proof.
move => ctg ne_sec'_sec mem_dom_mp_elem_sec'.
split => [tag' mem_tag'_hdb |].
rewrite -mem_frng frng_set in_fsetU1 mem_frng rem_id //#.
split => [elem' not_mem_dom_ec_elem' | elem' mem_dom_ec_elem'].
case (dom mp (elem', sec)) =>
  [mem_dom_mp_elem'_sec | not_mem_dom_mp_elem'_sec].
right; rewrite get_setE /#.
left; rewrite mem_set /#.
split.
by rewrite mem_set
           (counting_in_ec_dom_impl_in_dom_or sec hdb mp
            elems_cnts elem').
rewrite get_setE.
have -> /= : (elem', sec) <> (elem, sec') by smt().
have elem_sec_in_mp : (elem', sec) \in mp
  by apply (counting_in_ec_dom_impl_in_dom_or sec hdb mp elems_cnts).
smt().
qed.

lemma counting_num_occs_add_hdb_eq
  (sec : sec, hdb : hdb, mp : (elem * sec, tag) fmap,
   elems_cnts : elems_counts, elem : elem) :
  counting sec hdb mp elems_cnts =>
  dom mp (elem, sec) =>
  num_occs (oget mp.[(elem, sec)]) (hdb ++ [oget mp.[(elem, sec)]]) =
  oget (incr_count elems_cnts elem).[elem].
proof.
move => cntg mem_dom_mp_elem_sec.
rewrite /num_occs size_cat /= num_occs_upto_eq 1:size_cat /=.
smt(size_ge0). by rewrite nth_cat /=.
rewrite num_occs_upto_drop_last_part /incr_count.
case (dom elems_cnts elem) => [mem_dom_ec_elem | not_mem_dom_ec_elem];
  rewrite get_setE /= /#.
qed.

lemma counting_num_occs_add_hdb_ne_notin_ec
  (sec : sec, hdb : hdb, mp : (elem * sec, tag) fmap,
   elems_cnts : elems_counts, elem elem' : elem) :
  inj mp (frng mp) => counting sec hdb mp elems_cnts =>
  elem' <> elem => dom mp (elem, sec) =>
  ! dom elems_cnts elem' =>
  ! dom mp (elem', sec) \/
  num_occs (oget mp.[(elem', sec)]) (hdb ++ [oget mp.[(elem, sec)]]) = 0.
proof.
move => inj [_ [cntg2 _]] ne_elem'_elem mem_dom_mp_elem_sec
        not_mem_dom_ec_elem'.
case (dom mp (elem', sec)) => [mem_dom_mp_elem'_sec | //].
right.
have ne_tag_elem'_elem : oget mp.[(elem', sec)] <> oget mp.[(elem, sec)]
  by apply (inj_cancel_contra mp (frng mp) (elem', sec) (elem, sec)).
rewrite /num_occs size_cat /= num_occs_upto_ne 1:size_cat /=.
smt(size_ge0). rewrite nth_cat /#.
rewrite num_occs_upto_drop_last_part /#.
qed.

lemma counting_num_occs_add_hdb_ne_in_ec
  (sec : sec, hdb : hdb, mp : (elem * sec, tag) fmap,
   elems_cnts : elems_counts, elem elem' : elem) :
  inj mp (frng mp) => counting sec hdb mp elems_cnts =>
  elem' <> elem => dom mp (elem, sec) =>
  dom elems_cnts elem' =>
  dom mp (elem', sec) /\
  num_occs (oget mp.[(elem', sec)]) (hdb ++ [oget mp.[(elem, sec)]]) =
  oget elems_cnts.[elem'].
proof.
move => inj cntg ne_elem'_elem mem_dom_mp_elem_sec mem_dom_ec_elem'.
have mem_dom_mp_elem'_sec : dom mp (elem', sec)
  by apply (counting_in_ec_dom_impl_in_dom_or sec hdb mp elems_cnts elem').
split => //.
have ne_tag_elem'_elem : oget mp.[(elem', sec)] <> oget mp.[(elem, sec)]
  by apply (inj_cancel_contra mp (frng mp) (elem', sec) (elem, sec)).
rewrite /num_occs size_cat /= num_occs_upto_ne 1:size_cat /=.
smt(size_ge0). rewrite nth_cat /#.
rewrite num_occs_upto_drop_last_part /#.
qed.

lemma counting_add_in_or
  (sec : sec, hdb : hdb, mp : (elem * sec, tag) fmap,
   elems_cnts : elems_counts, elem : elem) :
  inj mp (frng mp) =>
  counting sec hdb mp elems_cnts =>
  dom mp (elem, sec) =>
  counting sec (hdb ++ [oget mp.[(elem, sec)]]) mp
           (incr_count elems_cnts elem).
proof.
move => inj cntg mem_dom_mp_elem_sec.
split => [tag mem_hdb_cat_get_elem_sec_tag |].
rewrite mem_cat /= in mem_hdb_cat_get_elem_sec_tag.
elim mem_hdb_cat_get_elem_sec_tag => [/# | ->].
rewrite rngE /=; exists (elem, sec); by rewrite get_some.
split => [elem' not_mem_dom_incr_ec_elem_elem' |].
rewrite -mem_fdom ec_incr_dom in_fsetU in_fset1
         negb_or in not_mem_dom_incr_ec_elem_elem'.
elim not_mem_dom_incr_ec_elem_elem' => [not_mem_dom_ec_elem' ne_elem'_elem].
  rewrite (counting_num_occs_add_hdb_ne_notin_ec sec hdb mp elems_cnts
           elem elem') //.
  smt(mem_fdom).
move => elem' mem_dom_incr_ec_elem_elem'.
rewrite -mem_fdom ec_incr_dom in_fsetU in_fset1 in mem_dom_incr_ec_elem_elem'.
case (elem' = elem) => [->> | ne_elem'_elem].
split => //; first by apply counting_num_occs_add_hdb_eq.
have mem_dom_ec_elem' : dom elems_cnts elem' by smt(mem_fdom).
split.
by apply (counting_in_ec_dom_impl_in_dom_or sec hdb mp elems_cnts elem').
have [_ ->] :=
  counting_num_occs_add_hdb_ne_in_ec sec hdb mp elems_cnts elem elem'
  inj cntg ne_elem'_elem mem_dom_mp_elem_sec mem_dom_ec_elem'.
by rewrite ec_incr_oget_in_dom_ne.
qed.

local lemma BOrInj_adv_bhash_counting
            (sec : sec, hdb : hdb, elems_cnts : elems_counts) :
  equiv
  [BRO.BOrInj.adv_bhash ~ BRO.BOrInj.adv_bhash :
   ={inp, glob BRO.BOrInj} /\
   BRO.BOrInj.adv_ctr{1} <= adv_budget /\
   BRO.BOrInj.serv_ctr{1} <= db_uniqs_max /\
   BRO.BOrInj.clnt_ctr{1} <= qrys_max /\
   (BRO.BOrInj.adv_ctr{1} < adv_budget => ! BRO.BOrInj.adv_over{1}) /\
   (! BRO.BOrInj.adv_over{1} =>
    inj BRO.BOrInj.mp{1} BRO.BOrInj.outs{1} /\
    counting sec hdb BRO.BOrInj.mp{1} elems_cnts) /\
   card BRO.BOrInj.outs{1} <=
   BRO.BOrInj.adv_ctr{1} + BRO.BOrInj.serv_ctr{1} + BRO.BOrInj.clnt_ctr{1} ==>
   ={res, glob BRO.BOrInj} /\ BRO.BOrInj.adv_ctr{1} <= adv_budget /\
   (BRO.BOrInj.adv_ctr{1} < adv_budget => ! BRO.BOrInj.adv_over{1}) /\
   (! BRO.BOrInj.adv_over{1} =>
    inj BRO.BOrInj.mp{1} BRO.BOrInj.outs{1} /\
    counting sec hdb BRO.BOrInj.mp{1} elems_cnts) /\
   card BRO.BOrInj.outs{1} <=
   BRO.BOrInj.adv_ctr{1} + BRO.BOrInj.serv_ctr{1} + BRO.BOrInj.clnt_ctr{1}].
proof.
proc.
if => //; first auto.
if => //.
if => //.
auto; smt().
seq 1 1 :
  (={inp, out, glob BRO.BOrInj} /\
   BRO.BOrInj.adv_ctr{1} <= adv_budget /\
   BRO.BOrInj.serv_ctr{1} <= db_uniqs_max /\
   BRO.BOrInj.clnt_ctr{1} <= qrys_max /\
   (BRO.BOrInj.adv_ctr{1} < adv_budget => ! BRO.BOrInj.adv_over{1}) /\
   (! BRO.BOrInj.adv_over{1} =>
    inj BRO.BOrInj.mp{1} BRO.BOrInj.outs{1} /\
    counting sec hdb BRO.BOrInj.mp{1} elems_cnts) /\
   card BRO.BOrInj.outs{1} <=
   BRO.BOrInj.adv_ctr{1} + BRO.BOrInj.serv_ctr{1} + BRO.BOrInj.clnt_ctr{1} /\
   ! mem BRO.BOrInj.adv_inps{1} inp{1} /\ BRO.BOrInj.adv_ctr{1} < adv_budget /\
   ! dom BRO.BOrInj.mp{1} inp{1}); first auto.
wp.
if => //.
auto => |> &2 _ le_serv_ctr_budg le_clnt_ctr_budg
        lt_adv_ctr_budg_imp_adv_not_over adv_not_over_imp_inj_cntg
        outs_ub_ctrs not_mem_inps_inp lt_adv_ctr_budg
        not_mem_dom_mp_inp mem_outs_out out'
        not_in_supp_out'_out_distr_min_outs.
have not_mem_outs_out' : ! mem BRO.BOrInj.outs{2} out'
  by rewrite (in_supp_minus_not_pred out' tag_distr (mem BRO.BOrInj.outs{2})).
split; first smt().
split; first smt().
split => [not_adv_over |].
have [inje ctg] := adv_not_over_imp_inj_cntg not_adv_over.
split; first by rewrite inj_add.
have -> : inp{2} = (fst inp{2}, snd inp{2}) by smt().
case (snd inp{2} = sec) => [eq_snd_inp2_sec | not_eq_snd_inp2_sec].
rewrite eq_snd_inp2_sec counting_add_or_new_sec; smt(mem_fdom mem_frng).
rewrite counting_add_or_new_non_sec /#.
rewrite fcardUI_indep 1:fsetI1 1:not_mem_outs_out' // fcard1 /#.
auto => |> &2 _ le_serv_ctr_budg le_clnt_ctr_budg
        lt_adv_ctr_budg_imp_adv_not_over adv_not_over_imp_inj_cntg
        outs_ub_ctrs not_mem_inps_inp lt_adv_ctr_budg
        not_mem_dom_mp_inp not_mem_outs_out.
split; first smt().
split; first smt().
split => [not_adv_over |].
have [inje ctg] := adv_not_over_imp_inj_cntg not_adv_over.
split; first by rewrite inj_add 1:/#.
have -> : inp{2} = (fst inp{2}, snd inp{2}) by smt().
case (snd inp{2} = sec) => [eq_snd_inp2_sec | not_eq_snd_inp2_sec].
rewrite eq_snd_inp2_sec counting_add_or_new_sec; smt(mem_fdom mem_frng).
rewrite counting_add_or_new_non_sec /#.
rewrite fcardUI_indep 1:fsetI1 1:not_mem_outs_out // fcard1 /#.
call (_ : ={glob BRO.BOrInj}).
if => //; auto.
auto.
qed.

local lemma BOrInj_server_bhash_counting_mem_inps
            (sec : sec, elem : elem, hdb : hdb, elems_cnts : elems_counts,
             serv_inps' : (elem * sec) fset) :
  equiv
  [BRO.BOrInj.server_bhash ~ BRO.BOrInj.server_bhash :
   ={inp, glob BRO.BOrInj} /\
   inp{1} = (elem, sec) /\ BRO.BOrInj.serv_inps{1} = serv_inps' /\
   BRO.BOrInj.serv_ctr{1} = card BRO.BOrInj.serv_inps{1} /\
   BRO.BOrInj.adv_ctr{1} <= adv_budget /\
   BRO.BOrInj.serv_ctr{1} <= db_uniqs_max /\
   BRO.BOrInj.clnt_ctr{1} = 0 /\
   BRO.BOrInj.serv_inps{1} \subset fdom BRO.BOrInj.mp{1} /\
   mem serv_inps' (elem, sec) /\ ! BRO.BOrInj.serv_over{1} /\
   inj BRO.BOrInj.mp{1} BRO.BOrInj.outs{1} /\
   counting sec hdb BRO.BOrInj.mp{1} elems_cnts /\
   card BRO.BOrInj.outs{1} <=
   BRO.BOrInj.adv_ctr{1} + BRO.BOrInj.serv_ctr{1} ==>
   ={res, glob BRO.BOrInj} /\ BRO.BOrInj.serv_ctr{1} <= db_uniqs_max /\
   BRO.BOrInj.serv_inps{1} \subset fdom BRO.BOrInj.mp{1} /\
   ! BRO.BOrInj.serv_over{1} /\
   inj BRO.BOrInj.mp{1} BRO.BOrInj.outs{1} /\
   counting sec hdb BRO.BOrInj.mp{1} elems_cnts /\
   card BRO.BOrInj.outs{1} <=
   BRO.BOrInj.adv_ctr{1} + BRO.BOrInj.serv_ctr{1} /\
   BRO.BOrInj.mp{1}.[(elem, sec)] = Some(res{1}) /\
   BRO.BOrInj.serv_inps{1} = serv_inps' /\
   BRO.BOrInj.serv_ctr{1} = card BRO.BOrInj.serv_inps{1}].
proof.
proc.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
auto; progress [-delta].
have mem_dom_mp_inp : dom BRO.BOrInj.mp{2} (elem, sec) by smt(mem_fdom).
by rewrite get_some.
qed.

local lemma BOrInj_server_bhash_counting_not_mem_inps
            (sec : sec, elem : elem, hdb : hdb, elems_cnts : elems_counts,
             serv_inps' : (elem * sec) fset) :
  equiv
  [BRO.BOrInj.server_bhash ~ BRO.BOrInj.server_bhash :
   ={inp, glob BRO.BOrInj} /\
   inp{1} = (elem, sec) /\ serv_inps' = BRO.BOrInj.serv_inps{1} /\
   BRO.BOrInj.serv_ctr{1} = card BRO.BOrInj.serv_inps{1} /\
   BRO.BOrInj.adv_ctr{1} <= adv_budget /\
   BRO.BOrInj.serv_ctr{1} < db_uniqs_max /\
   BRO.BOrInj.clnt_ctr{1} = 0 /\
   BRO.BOrInj.serv_inps{1} \subset fdom BRO.BOrInj.mp{1} /\
   ! mem serv_inps' (elem, sec) /\ ! BRO.BOrInj.serv_over{1} /\
   inj BRO.BOrInj.mp{1} BRO.BOrInj.outs{1} /\
   counting sec hdb BRO.BOrInj.mp{1} elems_cnts /\
   card BRO.BOrInj.outs{1} <=
   BRO.BOrInj.adv_ctr{1} + BRO.BOrInj.serv_ctr{1} ==>
   ={res, glob BRO.BOrInj} /\ BRO.BOrInj.serv_ctr{1} <= db_uniqs_max /\
   BRO.BOrInj.serv_inps{1} \subset fdom BRO.BOrInj.mp{1} /\
   ! BRO.BOrInj.serv_over{1} /\
   inj BRO.BOrInj.mp{1} BRO.BOrInj.outs{1} /\
   counting sec hdb BRO.BOrInj.mp{1} elems_cnts /\
   card BRO.BOrInj.outs{1} <=
   BRO.BOrInj.adv_ctr{1} + BRO.BOrInj.serv_ctr{1} /\
   BRO.BOrInj.mp{1}.[(elem, sec)] = Some(res{1}) /\
   BRO.BOrInj.serv_ctr{1} = card BRO.BOrInj.serv_inps{1} /\
   BRO.BOrInj.serv_inps{1} = serv_inps' `|` fset1 (elem, sec)].
proof.
proc.
rcondf{1} 1; first auto. rcondf{2} 1; first auto.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
if => //.
auto; progress [-delta];
  [smt() | move => inp' /in_fsetU1 [/# | -> //]; smt(mem_fdom) |
   smt(lez_addr) | by rewrite get_some |
   by rewrite fcardUI_indep 1:fsetI1 1:/# fcard1].
seq 1 1 :
  (={inp, out, glob BRO.BOrInj} /\
   inp{1} = (elem, sec) /\ serv_inps' = BRO.BOrInj.serv_inps{1} /\
   BRO.BOrInj.serv_ctr{1} = card BRO.BOrInj.serv_inps{1} /\
   BRO.BOrInj.adv_ctr{1} <= adv_budget /\
   BRO.BOrInj.serv_ctr{1} < db_uniqs_max /\
   BRO.BOrInj.clnt_ctr{1} = 0 /\
   BRO.BOrInj.serv_inps{1} \subset fdom BRO.BOrInj.mp{1} /\
   ! mem BRO.BOrInj.serv_inps{1} (elem, sec) /\ ! BRO.BOrInj.serv_over{1} /\
   inj BRO.BOrInj.mp{1} BRO.BOrInj.outs{1} /\
   counting sec hdb BRO.BOrInj.mp{1} elems_cnts /\
   card BRO.BOrInj.outs{1} <=
   BRO.BOrInj.adv_ctr{1} + BRO.BOrInj.serv_ctr{1} /\
   ! dom BRO.BOrInj.mp{1} inp{1}); first auto.
if => //.
auto =>
  |> &2 le_adv_ctr_budg card_serv_inps_lt_db_uniqs_max
  subset_inps_dom_mp not_mem_inps_elem_sec
  not_serv_over inje cntg outs_ub_ctrs not_mem_dom_mp_elem_sec
  mem_outs_out out' not_in_supp_out'_out_distr_min_outs.
have not_mem_outs_out' : ! mem BRO.BOrInj.outs{2} out'
  by rewrite (in_supp_minus_not_pred out' tag_distr (mem BRO.BOrInj.outs{2})).
split; first smt().
split.
move => inp'' /in_fsetU1 [mem_inps_inp'' | ->].
rewrite mem_fdom mem_set -mem_fdom /#.
rewrite mem_fdom mem_set /#.
split; first by apply inj_add.
split; first rewrite counting_add_or_new_sec; smt(mem_fdom mem_frng).
split; first rewrite fcardUI_indep 1:fsetI1 1:not_mem_outs_out' // fcard1 /#.
split; first by rewrite get_set_sameE.
by rewrite fcardUI_indep 1:fsetI1 1:/# fcard1.
auto =>
  |> &2 le_adv_ctr_budg card_serv_inps_lt_db_uniqs_max
  subset_inps_dom_mp not_mem_inps_elem_sec not_serv_over inje cntg
  outs_ub_ctrs not_mem_dom_mp_elem_sec not_mem_outs_out.
split; first smt().
split.
move => inp'' /in_fsetU1 [mem_inps_inp'' | ->].
rewrite mem_fdom mem_set -mem_fdom /#.
rewrite mem_fdom mem_set /#.
split; first by apply inj_add.
split; first rewrite counting_add_or_new_sec; smt(mem_fdom mem_frng).
split; first rewrite fcardUI_indep 1:fsetI1 1:not_mem_outs_out // fcard1 /#.
split; first by rewrite get_set_sameE.
by rewrite fcardUI_indep 1:fsetI1 1:/# fcard1.
qed.

local lemma BOrInj_client_bhash_counting
            (sec : sec, elem : elem, hdb : hdb, elems_cnts : elems_counts,
             clnt_ctr' : int) :
  equiv
  [BRO.BOrInj.client_bhash ~ BRO.BOrInj.client_bhash :
   ={inp, glob BRO.BOrInj} /\ inp{1} = (elem, sec) /\
   clnt_ctr' = BRO.BOrInj.clnt_ctr{1} /\
   BRO.BOrInj.adv_ctr{1} <= adv_budget /\
   BRO.BOrInj.serv_ctr{1} <= db_uniqs_max /\
   BRO.BOrInj.clnt_ctr{1} < qrys_max /\ ! BRO.BOrInj.clnt_over{1} /\
   inj BRO.BOrInj.mp{1} BRO.BOrInj.outs{1} /\
   counting sec hdb BRO.BOrInj.mp{1} elems_cnts /\
   card BRO.BOrInj.outs{1} <=
   BRO.BOrInj.adv_ctr{1} + BRO.BOrInj.serv_ctr{1} + BRO.BOrInj.clnt_ctr{1} ==>
   ={res, glob BRO.BOrInj} /\ BRO.BOrInj.clnt_ctr{1} <= qrys_max /\
   ! BRO.BOrInj.clnt_over{1} /\
   inj BRO.BOrInj.mp{1} BRO.BOrInj.outs{1} /\
   counting sec hdb BRO.BOrInj.mp{1} elems_cnts /\
   card BRO.BOrInj.outs{1} <=
   BRO.BOrInj.adv_ctr{1} + BRO.BOrInj.serv_ctr{1} + BRO.BOrInj.clnt_ctr{1} /\
   BRO.BOrInj.mp{1}.[(elem, sec)] = Some(res{1}) /\
   BRO.BOrInj.clnt_ctr{1} = clnt_ctr' + 1].
proof.
proc.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
if => //.
auto; progress [-delta]; [smt() | smt() | by rewrite get_some].
seq 1 1 :
  (={inp, out, glob BRO.BOrInj} /\
   inp{1} = (elem, sec) /\ clnt_ctr' = BRO.BOrInj.clnt_ctr{1} /\
   BRO.BOrInj.adv_ctr{1} <= adv_budget /\
   BRO.BOrInj.serv_ctr{1} <= db_uniqs_max /\
   BRO.BOrInj.clnt_ctr{1} < qrys_max /\ ! BRO.BOrInj.clnt_over{1} /\
   inj BRO.BOrInj.mp{1} BRO.BOrInj.outs{1} /\
   counting sec hdb BRO.BOrInj.mp{1} elems_cnts /\
   card BRO.BOrInj.outs{1} <=
   BRO.BOrInj.adv_ctr{1} + BRO.BOrInj.serv_ctr{1} + BRO.BOrInj.clnt_ctr{1} /\
   ! dom BRO.BOrInj.mp{1} inp{1}); first auto.
wp.
if => //.
auto => |> &2 le_adv_ctr_budg le_serv_ctr_budg lt_clnt_ctr_budg
        not_clnt_over inje cntg outs_ub_ctrs not_mem_dom_mp_elem_sec
        mem_outs_out out' not_in_supp_out'_out_distr_min_outs.
have not_mem_outs_out' : ! mem BRO.BOrInj.outs{2} out'
  by rewrite (in_supp_minus_not_pred out' tag_distr (mem BRO.BOrInj.outs{2})).
split; first smt().
split; first by apply inj_add.
split; first rewrite counting_add_or_new_sec; smt(mem_fdom mem_frng).
split; first rewrite fcardUI_indep 1:fsetI1 1:not_mem_outs_out' // fcard1 /#.
by rewrite get_set_sameE.
auto => |> &2 le_adv_ctr_budg le_serv_ctr_budg lt_clnt_ctr_budg
        not_clnt_over inje cntg outs_ub_ctrs not_mem_dom_mp_elem_sec
        not_mem_outs_out.
split; first smt().
split; first by apply inj_add.
split; first rewrite counting_add_or_new_sec; smt(mem_fdom mem_frng).
split; first rewrite fcardUI_indep 1:fsetI1 1:not_mem_outs_out // fcard1 /#.
by rewrite get_set_sameE.
qed.

(* server metric -- division of server's database hashing into inputs
   already hashed and distinct elements not already hashed in part of
   database yet to be processed *)

op serv_metric
   (sec : sec, i : int, inps : (elem * sec) fset, db : elem list) : int =
  card inps + 
  card
  (image (fun (elem : elem) => (elem, sec)) (oflist (drop i db)) `\`
   inps).

lemma serv_metric0_bound (sec : sec, db : elem list) :
  num_uniqs db <= db_uniqs_max =>
  serv_metric sec 0 fset0 db <= db_uniqs_max.
proof.
move => num_uniqs_db_le_db_uniqs_max.
by rewrite /serv_metric drop0 fsetD0 fcards0 /= (lez_trans (card(oflist db)))
           1:fcard_image_leq.
qed.

lemma serv_metric_bound_imp_card_inps_bound
      (sec : sec, i : int, inps : (elem * sec) fset, db : elem list) :
  serv_metric sec i inps db <= db_uniqs_max =>
  card inps <= db_uniqs_max.
proof.
move => serv_met; smt(fcard_ge0).
qed.

lemma serv_metric_not_mem_bound_imp_card_inps_strict_bound
      (sec : sec, i : int, inps : (elem * sec) fset, db : elem list) :
  0 <= i < size db => ! mem inps (nth elem_default db i, sec) =>
  serv_metric sec i inps db <= db_uniqs_max =>
  card inps < db_uniqs_max.
proof.
move => [ge0_i i_lt_sz_db] not_mem_inps_elem_sec serv_met.
rewrite /serv_metric in serv_met.
have non_nil_image_i_min_inps :
  image (fun (elem : elem) => (elem, sec)) (oflist (drop i db)) `\`
  inps <> fset0.
  rewrite (drop_nth elem_default) // oflist_cons imageU image1 fsetDUl
          fset1D not_mem_inps_elem_sec /=.
  pose xs := image _ _ `\` _.
  case (fset1 (nth elem_default db i, sec) `|` xs = fset0) => // contrad.
  rewrite fsetP in contrad.
  have contrad' := contrad (nth elem_default db i, sec).
  rewrite in_fset0 fsetUC in_fsetU1 /# in contrad'.
smt(fcard_ge0 fcard_eq0).
qed.

lemma serv_metric_mem_step
      (sec : sec, i : int, inps : (elem * sec) fset, db : elem list) :
  0 <= i < size db => mem inps (nth elem_default db i, sec) =>
  serv_metric sec i inps db = serv_metric sec (i + 1) inps db.
proof.
move => [ge0_i lt_i_sz_db] mem_inps_elem_sec.
rewrite /serv_metric.
have -> // :
  image (fun (elem : elem) => (elem, sec)) (oflist (drop i db)) `\` inps =
  image (fun (elem : elem) => (elem, sec)) (oflist (drop (i + 1) db)) `\`
  inps
  by rewrite (drop_nth elem_default i) // oflist_cons imageU image1 fsetDUl
             fset1D /= mem_inps_elem_sec /= fset0U.
qed.

lemma serv_metric_not_mem_step
      (sec : sec, i : int, inps : (elem * sec) fset, db : elem list) :
  0 <= i < size db => ! mem inps (nth elem_default db i, sec) =>
  serv_metric sec i inps db =
  serv_metric sec (i + 1) (inps `|` fset1 (nth elem_default db i, sec)) db.
proof.
move => [ge0_i lt_i_sz_db] not_mem_inps_elem_sec.
rewrite /serv_metric.
rewrite (drop_nth elem_default i) // oflist_cons imageU image1 /=
        fsetDUl fset1D not_mem_inps_elem_sec /= (fcardUI_indep inps)
        1:fsetI1 1:not_mem_inps_elem_sec // fcard1. 
pose us := image _ _.
case (mem us (nth elem_default db i, sec)) =>
  [mem_us_elem_sec | not_mem_us_elem_sec].
rewrite (subset_fsetU_id (fset1 (nth elem_default db i, sec))).
move => x; by rewrite in_fset1 in_fsetD.
rewrite 2!fcardD 2!fcardI
        (fcardUI_indep inps (fset1 (nth elem_default db i, sec)))
        1:fsetI1 1:not_mem_inps_elem_sec // fcard1 (fsetUC inps) fsetUA
        (fsetUC us (fset1 (nth elem_default db i, sec))).
rewrite (subset_fsetU_id (fset1 (nth elem_default db i, sec))).
move => x; rewrite in_fset1 => -> //.
algebra.
rewrite -fsetDDl (fcardD (us `\` inps)) fsetI1 in_fsetD
       not_mem_inps_elem_sec not_mem_us_elem_sec fcards0 /=.
rewrite fcardUI_indep 1:fset1I 1:in_fsetD 1:not_mem_us_elem_sec // fcard1.
algebra.
qed.

local lemma G2_server_hash_db_G3_server_hash_and_count_db :
  equiv
  [G2.server_hash_db ~ G3.server_count_and_hash_db :
   ={db, glob BRO.BOrInj} /\ ={sec}(G2, G3) /\
   num_uniqs db{1} <= db_uniqs_max /\
   BRO.BOrInj.adv_ctr{1} <= adv_budget /\
   BRO.BOrInj.clnt_ctr{1} = 0 /\ BRO.BOrInj.serv_ctr{1} = 0 /\
   BRO.BOrInj.serv_inps{1} = fset0 /\
   ! BRO.BOrInj.serv_over{1} /\
   inj BRO.BOrInj.mp{1} BRO.BOrInj.outs{1} /\
   counting G2.sec{1} [] BRO.BOrInj.mp{1} empty_ec /\
   card BRO.BOrInj.outs{1} <= BRO.BOrInj.adv_ctr{1} ==>
   ={glob BRO.BOrInj} /\
   BRO.BOrInj.serv_ctr{1} <= db_uniqs_max /\
   ! BRO.BOrInj.serv_over{1} /\
   inj BRO.BOrInj.mp{1} BRO.BOrInj.outs{1} /\
   counting G2.sec{1} G2.hdb{1} BRO.BOrInj.mp{1} G3.elems_cnts{2} /\
   card BRO.BOrInj.outs{1} <=
   BRO.BOrInj.adv_ctr{1} + BRO.BOrInj.serv_ctr{1}].
proof.
proc.
seq 3 3 :
  (={db, i, glob BRO.BOrInj} /\ i{1} = 0 /\ ={sec}(G2, G3) /\
   G2.hdb{1} = [] /\ G3.elems_cnts{2} = empty_ec /\
   num_uniqs db{1} <= db_uniqs_max /\
   BRO.BOrInj.adv_ctr{1} <= adv_budget /\
   BRO.BOrInj.clnt_ctr{1} = 0 /\
   BRO.BOrInj.serv_ctr{1} = 0 /\ BRO.BOrInj.serv_inps{1} = fset0 /\
   ! BRO.BOrInj.serv_over{1} /\
   inj BRO.BOrInj.mp{1} BRO.BOrInj.outs{1} /\
   counting G2.sec{1} [] BRO.BOrInj.mp{1} empty_ec /\
   card BRO.BOrInj.outs{1} <= BRO.BOrInj.adv_ctr{1}).
wp; exists* db{1}; elim* => db'.
call (_ : ={xs} /\ xs{1} = db' ==> ={res} /\ perm_eq res{1} db').
apply (Shuffle_shuffle_perm db').
skip; progress; smt(oflist_perm_eq).
while
  (={db, i, glob BRO.BOrInj} /\ ={sec}(G2, G3) /\
   0 <= i{1} /\ i{1} <= size db{1} /\
   BRO.BOrInj.adv_ctr{1} <= adv_budget /\
   BRO.BOrInj.clnt_ctr{1} = 0 /\
   BRO.BOrInj.serv_ctr{1} = card BRO.BOrInj.serv_inps{1} /\
   BRO.BOrInj.serv_inps{1} \subset fdom BRO.BOrInj.mp{1} /\
   serv_metric G2.sec{1} i{1} BRO.BOrInj.serv_inps{1} db{1} <= db_uniqs_max /\
   ! BRO.BOrInj.serv_over{1} /\
   inj BRO.BOrInj.mp{1} BRO.BOrInj.outs{1} /\
   counting G2.sec{1} G2.hdb{1} BRO.BOrInj.mp{1} G3.elems_cnts{2} /\
   card BRO.BOrInj.outs{1} <=
   BRO.BOrInj.adv_ctr{1} + BRO.BOrInj.serv_ctr{1}).
sp; wp.
elim* => elems_cnts'.
exists* G2.sec{1}; elim* => sec'.
exists* elem{1}; elim* => elem'.
exists* G2.hdb{1}; elim* => hdb'.
exists* BRO.BOrInj.serv_inps{1}; elim* => serv_inps'.
case (mem serv_inps' (elem', sec')).
call 
  (BOrInj_server_bhash_counting_mem_inps
   sec' elem' hdb' elems_cnts' serv_inps').
auto =>
 |> &2 ge0_i _ adv_ctr_le_adv_bud serv_inps_sub_dom_mp
  serv_metric_invar not_serv_over inje cntg card_outs_ub i_lt_sz_db
  mem_serv_inps_elem_sec.
split => [| _]; first smt(fcard_ge0).
move =>
  result_R mp_R outs_R serv_over_R card_serv_inps_le_db_uniqs_max
  serv_inps_sub_dom_mp_r not_serv_over_R inje_R cntg_R card_outs_R_ub
  mp_R_lu_eq. 
split; first smt().
split; first smt().
split; first by rewrite -serv_metric_mem_step.


have -> :
  result_R = oget mp_R.[(nth elem_default db{2} i{2}, sec')]
  by rewrite mp_R_lu_eq.
apply counting_add_in_or => |>.
smt().
have :
  mp_R.[(nth elem_default db{2} i{2}, sec')] <> None by smt().
smt(domE).
call 
  (BOrInj_server_bhash_counting_not_mem_inps
   sec' elem' hdb' elems_cnts' serv_inps').
auto =>
 |> &2 ge0_i _ adv_ctr_le_adv_bud serv_inps_sub_dom_mp
  serv_metric_invar not_serv_over inje cntg card_outs_ub i_lt_sz_db
  mem_serv_inps_elem_sec.
split => [| _].
by rewrite
   (serv_metric_not_mem_bound_imp_card_inps_strict_bound sec' i{2}
    serv_inps' db{2}).
move =>
  result_R mp_R outs_R serv_over_R card_serv_new_inps_le_db_uniqs_max
  serv_new_inps_sub_dom_mp_r not_serv_over_R inje_R cntg_R card_outs_R_ub
  mp_R_lu_eq. 
split; first smt().
split; first smt().
split; first by rewrite -serv_metric_not_mem_step.
have -> :
  result_R = oget mp_R.[(nth elem_default db{2} i{2}, sec')]
  by rewrite mp_R_lu_eq.
apply counting_add_in_or => |>.
smt().
have :
  mp_R.[(nth elem_default db{2} i{2}, sec')] <> None by smt().
smt(domE).
auto; progress [-delta].
rewrite size_ge0.
by rewrite fcards0.
rewrite sub0set.
by rewrite serv_metric0_bound.
by rewrite
   (serv_metric_bound_imp_card_inps_bound G3.sec{2} i_R serv_inps_R db{2}).
qed.

local lemma G2_G3_client_loop :
  equiv
  [G2.client_loop ~ G3.client_loop :
   ={glob BRO.BOrInj, glob Adv} /\ ={sec, cv, qrys_ctr}(G2, G3) /\
   BRO.BOrInj.adv_ctr{1} <= adv_budget /\
   BRO.BOrInj.serv_ctr{1} <= db_uniqs_max /\
   G2.qrys_ctr{1} = 0 /\ BRO.BOrInj.clnt_ctr{1} = 0 /\ 
   ! BRO.BOrInj.adv_over{1} /\ ! BRO.BOrInj.clnt_over{1} /\
   inj BRO.BOrInj.mp{1} BRO.BOrInj.outs{1} /\
   counting G2.sec{1} G2.hdb{1} BRO.BOrInj.mp{1} G3.elems_cnts{2} /\
   card BRO.BOrInj.outs{1} <=
   BRO.BOrInj.adv_ctr{1} + BRO.BOrInj.serv_ctr{1} ==>
   ={glob BRO.BOrInj, glob Adv} /\ ={sec, cv, qrys_ctr}(G2, G3) /\
   BRO.BOrInj.clnt_ctr{1} <= qrys_max /\
   ! BRO.BOrInj.clnt_over{1} /\
   (BRO.BOrInj.adv_ctr{1} < adv_budget => ! BRO.BOrInj.adv_over{1}) /\
   (! BRO.BOrInj.adv_over{1} =>
    inj BRO.BOrInj.mp{1} BRO.BOrInj.outs{1} /\
    counting G2.sec{1} G2.hdb{1} BRO.BOrInj.mp{1} G3.elems_cnts{2}) /\
   card BRO.BOrInj.outs{1} <=
   BRO.BOrInj.adv_ctr{1} + BRO.BOrInj.serv_ctr{1} + BRO.BOrInj.clnt_ctr{1}].
proof.
proc; sp.
while
  (={not_done, glob BRO.BOrInj, glob Adv} /\ ={sec, cv, qrys_ctr}(G2, G3) /\
   BRO.BOrInj.adv_ctr{1} <= adv_budget /\
   BRO.BOrInj.serv_ctr{1} <= db_uniqs_max /\
   BRO.BOrInj.clnt_ctr{1} <= qrys_max /\
   BRO.BOrInj.clnt_ctr{1} = G2.qrys_ctr{1} /\
   ! BRO.BOrInj.clnt_over{1} /\
   (BRO.BOrInj.adv_ctr{1} < adv_budget => ! BRO.BOrInj.adv_over{1}) /\
   (! BRO.BOrInj.adv_over{1} =>
    inj BRO.BOrInj.mp{1} BRO.BOrInj.outs{1} /\
    counting G2.sec{1} G2.hdb{1} BRO.BOrInj.mp{1} G3.elems_cnts{2}) /\
   card BRO.BOrInj.outs{1} <=
   BRO.BOrInj.adv_ctr{1} + BRO.BOrInj.serv_ctr{1} + BRO.BOrInj.clnt_ctr{1}).
seq 1 1 :
  (={qry_opt, not_done, glob BRO.BOrInj, glob Adv} /\
   ={sec, cv, qrys_ctr}(G2, G3) /\
   BRO.BOrInj.adv_ctr{1} <= adv_budget /\
   BRO.BOrInj.serv_ctr{1} <= db_uniqs_max /\
   BRO.BOrInj.clnt_ctr{1} <= qrys_max /\
   BRO.BOrInj.clnt_ctr{1} = G2.qrys_ctr{1} /\
   ! BRO.BOrInj.clnt_over{1} /\
   (BRO.BOrInj.adv_ctr{1} < adv_budget => ! BRO.BOrInj.adv_over{1}) /\
   (! BRO.BOrInj.adv_over{1} =>
    inj BRO.BOrInj.mp{1} BRO.BOrInj.outs{1} /\
    counting G2.sec{1} G2.hdb{1} BRO.BOrInj.mp{1} G3.elems_cnts{2}) /\
   card BRO.BOrInj.outs{1} <=
   BRO.BOrInj.adv_ctr{1} + BRO.BOrInj.serv_ctr{1} + BRO.BOrInj.clnt_ctr{1}).
call
  (_ :
   ={glob BRO.BOrInj} /\
   BRO.BOrInj.adv_ctr{1} <= adv_budget /\
   BRO.BOrInj.serv_ctr{1} <= db_uniqs_max /\
   BRO.BOrInj.clnt_ctr{1} <= qrys_max /\
   (BRO.BOrInj.adv_ctr{1} < adv_budget => ! BRO.BOrInj.adv_over{1}) /\
   (! BRO.BOrInj.adv_over{1} =>
    inj BRO.BOrInj.mp{1} BRO.BOrInj.outs{1} /\
    counting G2.sec{1} G2.hdb{1} BRO.BOrInj.mp{1} G3.elems_cnts{2}) /\
   card BRO.BOrInj.outs{1} <=
   BRO.BOrInj.adv_ctr{1} + BRO.BOrInj.serv_ctr{1} + BRO.BOrInj.clnt_ctr{1}).
proc.
exists* G2.sec{1}; elim* => sec'.
exists* G2.hdb{1}; elim* => hdb'.
exists* G3.elems_cnts{2}; elim* => elems_cnts'.
call (BOrInj_adv_bhash_counting sec' hdb' elems_cnts').
auto. auto.
if => //.
auto.
inline BRO.BOrInj.adv_within_budget; sp.
if => //.
exists* G2.sec{1}; elim* => sec'.
exists* qry_opt{1}; elim* => qry_opt'.
exists* G2.hdb{1}; elim* => hdb'.
exists* G3.elems_cnts{2}; elim* => elems_cnts'.
exists* G2.qrys_ctr{1}; elim* => qrys_ctr'.
seq 3 3 :
  (={tag, qry_opt, not_done, glob BRO.BOrInj, glob Adv} /\
   ={sec, cv, qrys_ctr}(G2, G3) /\
   qry_opt' = qry_opt{1} /\ sec' = G2.sec{1} /\
   BRO.BOrInj.adv_ctr{1} <= adv_budget /\
   BRO.BOrInj.serv_ctr{1} <= db_uniqs_max /\
   BRO.BOrInj.clnt_ctr{1} <= qrys_max /\
   BRO.BOrInj.clnt_ctr{1} = G2.qrys_ctr{1} /\
   !BRO.BOrInj.adv_over{2} /\ ! BRO.BOrInj.clnt_over{1} /\
   inj BRO.BOrInj.mp{1} BRO.BOrInj.outs{1} /\
   counting G2.sec{1} G2.hdb{1} BRO.BOrInj.mp{1} G3.elems_cnts{2} /\
   card BRO.BOrInj.outs{1} <=
   BRO.BOrInj.adv_ctr{1} + BRO.BOrInj.serv_ctr{1} + BRO.BOrInj.clnt_ctr{1} /\
   BRO.BOrInj.mp{1}.[(oget qry_opt', sec')] = Some(tag{1})).
call (BOrInj_client_bhash_counting sec' (oget qry_opt') hdb' elems_cnts'
      qrys_ctr').
auto; progress [-delta]; smt().
seq 1 1 :
  (={cnt, tag, qry_opt, not_done, glob BRO.BOrInj, glob Adv} /\
   ={sec, cv, qrys_ctr}(G2, G3) /\ sec' = G2.sec{1} /\
   BRO.BOrInj.adv_ctr{1} <= adv_budget /\
   BRO.BOrInj.serv_ctr{1} <= db_uniqs_max /\
   BRO.BOrInj.clnt_ctr{1} <= qrys_max /\
   BRO.BOrInj.clnt_ctr{1} = G2.qrys_ctr{1} /\
   !BRO.BOrInj.adv_over{2} /\ ! BRO.BOrInj.clnt_over{1} /\
   inj BRO.BOrInj.mp{1} BRO.BOrInj.outs{1} /\
   counting G2.sec{1} G2.hdb{1} BRO.BOrInj.mp{1} G3.elems_cnts{2} /\
   card BRO.BOrInj.outs{1} <=
   BRO.BOrInj.adv_ctr{1} + BRO.BOrInj.serv_ctr{1} + BRO.BOrInj.clnt_ctr{1} /\
   BRO.BOrInj.mp{1}.[(oget qry_opt', sec')] = Some(tag{1})).
inline G3.tp_count_elem; sp.
inline G2.tp_count_tag; wp; sp.
while {1}
  (0 <= i{1} /\ i{1} <= size G2.hdb{1} /\
   cnt0{1} = num_occs_upto tag0{1} G2.hdb{1} i{1})
  (size G2.hdb{1} - i{1}).
auto; smt(size_ge0 num_occs_upto_eq nth_in_range num_occs_upto_ne).
auto; progress;
  [smt(size_ge0) | smt(num_occs_upto0) | smt() |
   smt(counting_num_occs_get_count)].
call
  (_ :
   ={glob BRO.BOrInj} /\
   BRO.BOrInj.adv_ctr{1} <= adv_budget /\
   BRO.BOrInj.serv_ctr{1} <= db_uniqs_max /\
   BRO.BOrInj.clnt_ctr{1} <= qrys_max /\
   (BRO.BOrInj.adv_ctr{1} < adv_budget => ! BRO.BOrInj.adv_over{1}) /\
   (! BRO.BOrInj.adv_over{1} =>
    inj BRO.BOrInj.mp{1} BRO.BOrInj.outs{1} /\
    counting G2.sec{1} G2.hdb{1} BRO.BOrInj.mp{1} G3.elems_cnts{2}) /\
   card BRO.BOrInj.outs{1} <=
   BRO.BOrInj.adv_ctr{1} + BRO.BOrInj.serv_ctr{1} + BRO.BOrInj.clnt_ctr{1}).
proc.
clear sec' hdb' elems_cnts'.
exists* G2.sec{1}; elim* => sec'.
exists* G2.hdb{1}; elim* => hdb'.
exists* G3.elems_cnts{2}; elim* => elems_cnts'.
call (BOrInj_adv_bhash_counting sec' hdb' elems_cnts').
auto.
auto.
auto.
auto; progress; apply qrys_max_ge0.
qed.

local lemma G2_G3_main :
  equiv[G2.main ~ G3.main : true ==> ={res}].
proof.
proc.
seq 4 4 :
  (={glob BRO.BOrInj} /\ ={sec, cv, qrys_ctr}(G2, G3) /\
   G2.qrys_ctr{1} = 0 /\
   BRO.BOrInj.mp{1} = empty /\ BRO.BOrInj.outs{1} = fset0 /\
   BRO.BOrInj.adv_ctr{1} = 0 /\ BRO.BOrInj.adv_inps{1} = fset0 /\
   ! BRO.BOrInj.adv_over{1} /\
   BRO.BOrInj.serv_ctr{1} = 0 /\ BRO.BOrInj.serv_inps{1} = fset0 /\
   ! BRO.BOrInj.serv_over{1} /\
   BRO.BOrInj.clnt_ctr{1} = 0 /\ !BRO.BOrInj.clnt_over{1} /\
   inj BRO.BOrInj.mp{1} BRO.BOrInj.outs{1} /\
   counting G2.sec{1} [] BRO.BOrInj.mp{1} empty_ec).
inline*.
auto; progress [-delta];
  [apply inj_empty | apply counting_empty].
seq 1 1 :
  (={db_opt, glob BRO.BOrInj, glob Adv} /\ ={sec, cv, qrys_ctr}(G2, G3) /\
   G2.qrys_ctr{1} = 0 /\
   BRO.BOrInj.serv_ctr{1} = 0 /\ BRO.BOrInj.serv_inps{1} = fset0 /\
   ! BRO.BOrInj.serv_over{1} /\
   BRO.BOrInj.clnt_ctr{1} = 0 /\ !BRO.BOrInj.clnt_over{1} /\
   BRO.BOrInj.adv_ctr{1} <= adv_budget /\
   (BRO.BOrInj.adv_ctr{1} < adv_budget => ! BRO.BOrInj.adv_over{1}) /\
   (! BRO.BOrInj.adv_over{1} =>
    inj BRO.BOrInj.mp{1} BRO.BOrInj.outs{1} /\
    counting G2.sec{1} [] BRO.BOrInj.mp{1} empty_ec) /\
   card BRO.BOrInj.outs{1} <=
   BRO.BOrInj.adv_ctr{1} + BRO.BOrInj.serv_ctr{1} + BRO.BOrInj.clnt_ctr{1}).
call
  (_ :
   ={glob BRO.BOrInj} /\
   BRO.BOrInj.adv_ctr{1} <= adv_budget /\
   BRO.BOrInj.serv_ctr{1} <= db_uniqs_max /\
   BRO.BOrInj.clnt_ctr{1} <= qrys_max /\
   (BRO.BOrInj.adv_ctr{1} < adv_budget => ! BRO.BOrInj.adv_over{1}) /\
   (! BRO.BOrInj.adv_over{1} =>
    inj BRO.BOrInj.mp{1} BRO.BOrInj.outs{1} /\
    counting G2.sec{1} [] BRO.BOrInj.mp{1} empty_ec) /\
   card BRO.BOrInj.outs{1} <=
   BRO.BOrInj.adv_ctr{1} + BRO.BOrInj.serv_ctr{1} + BRO.BOrInj.clnt_ctr{1}).
proc.
exists* G2.sec{1}; elim* => sec'.
call (BOrInj_adv_bhash_counting sec' [] empty_ec).
auto.
auto; progress [-delta];
  [apply adv_budget_ge0 | apply db_uniqs_max_ge0 |
   apply qrys_max_ge0 | by rewrite fcards0].
call (_ : ={glob BRO.BOrInj}); first sim.
if => //.
inline BRO.BOrInj.adv_within_budget; sp.
if => //.
call G2_G3_client_loop.
call G2_server_hash_db_G3_server_hash_and_count_db.
auto; progress [-delta]; smt().
qed.

local lemma G2_G3 &m :
  Pr[G2.main() @ &m : res] = Pr[G3.main() @ &m : res].
proof. by byequiv G2_G3_main. qed.

local lemma GReal_G3 &m :
  `|Pr[GReal(Adv).main() @ &m : res] - Pr[G3.main() @ &m : res]| <=
   BRO.coll_bound.
proof. rewrite -(G2_G3 &m) (GReal_G2 &m). qed.

(* G4 is like H2 except it uses oracle BRO.BOr, instead of being
   parameterized by an oracle *)

local module G4 = H2(BRO.BOr).

(* we apply the Switching lemma to G4/G3

   our concrete switching adversary H2' is the same as H2, except that
   its main procedure doesn't (can't!) initialize the oracle, and
   elems_cnts is always initialized *)

local module (H2' : BRO.SWADV) (O : BRO.BOR) = {
  module A = Adv(BOrToCOr(O))

  var cv : client_view
  var sec : sec
  var elems_cnts : elems_counts
  var qrys_ctr : int

  proc server_count_and_hash_db(db : db) : unit = {
    var i : int; var elem : elem; var tag : tag;
    db <- Shuffle.shuffle(db);
    elems_cnts <- empty_ec; i <- 0;
    while (i < size db) {
      elem <- nth elem_default db i;
      elems_cnts <- incr_count elems_cnts elem;
      tag <@ O.server_bhash((elem, sec));
      i <- i + 1;
    }
  }

  proc tp_count_elem(attr : elem) : int = {
    return get_count elems_cnts attr;
  }

  proc client_loop() : unit = {
    var cnt : int; var tag : tag; var qry_opt : elem option;
    var not_done : bool <- true;
    var adv_within_budg : bool;
    while (not_done) {
      qry_opt <@ A.get_qry(cv);
      if (qry_opt = None) {
        not_done <- false;
        cv <- cv ++ [cv_got_qry None];
      }
      else {
        adv_within_budg <@ O.adv_within_budget();
        if (qrys_ctr < qrys_max /\ adv_within_budg) {
          cv <- cv ++ [cv_got_qry qry_opt];
          qrys_ctr <- qrys_ctr + 1;
          tag <@ O.client_bhash((oget qry_opt, sec));
          cnt <@ tp_count_elem(oget qry_opt);
          cv <- cv ++ [cv_query_count(oget qry_opt, tag, cnt)];
          A.qry_done(cv);
        }
        else {
          not_done <- false;
          cv <- cv ++ [cv_got_qry None];
        }
      }
    }
  }

  proc main() : bool = {
    var db_opt : db option;
    var b : bool;
    var adv_within_budg : bool;
    sec <$ sec_distr;
    cv <- [cv_got_sec sec];
    qrys_ctr <- 0; 
    elems_cnts <- empty_ec;
    db_opt <@ A.init_and_get_db(cv);
    if (db_opt <> None) {
      adv_within_budg <@ O.adv_within_budget();
      if (num_uniqs (oget db_opt) <= db_uniqs_max /\ adv_within_budg) {
        server_count_and_hash_db(oget db_opt);
        client_loop();
      }
    }
    b <@ A.final(cv);
    return b;
  }
}.

(* we work up to showing losslessness of H2'.main *)

local lemma H2'_server_count_and_hash_db_ll :
  forall (O <: BRO.BOR),
  islossless O.server_bhash => islossless H2'(O).server_count_and_hash_db.
proof.
move => O server_bhash_ll; proc.
while (true) (size db - i).
move => z; wp.
call (_ : true ==> true).
auto; smt().
wp.
call (_ : true ==> true); first apply Shuffle_shuffle_ll.
auto; smt().
qed.

local lemma H2'_tp_count_elem_ll :
  forall (O <: BRO.BOR),
  islossless H2'(O).tp_count_elem.
proof. move => O; proc; auto. qed.

local lemma H2'_client_loop_ll :
  forall (O <: BRO.BOR{H2'}),
  islossless O.adv_bhash => islossless O.adv_within_budget =>
  islossless O.server_bhash => islossless O.client_bhash =>
  islossless O.hash =>
  phoare
  [H2'(O).client_loop :
   H2'.qrys_ctr <= qrys_max ==> true] = 1%r.
proof.
move =>
  O adv_bhash_ll adv_within_budget_ll server_bhash_ll
  client_bhash_ll hash_ll.
proc; sp.
while (H2'.qrys_ctr <= qrys_max)
      (b2i not_done * (qrys_max - H2'.qrys_ctr + 1)).
auto.
seq 1 :
  (H2'.qrys_ctr <= qrys_max /\ not_done /\
   b2i not_done * (qrys_max - H2'.qrys_ctr + 1) = z).
auto.
call (_ : true ==> true).
apply (get_qry_ll (BOrToCOr(O))); proc; call adv_bhash_ll; auto.
auto.
if.
auto; smt().
seq 1 :
  (H2'.qrys_ctr <= qrys_max /\ not_done /\
   b2i not_done * (qrys_max - H2'.qrys_ctr + 1) = z).
call (_ : true); first auto.
call adv_within_budget_ll; auto.
if.
call (_ : true ==> true).
apply (qry_done_ll (BOrToCOr(O))); proc; call adv_bhash_ll; auto.
wp.
call (H2'_tp_count_elem_ll O).
call client_bhash_ll.
auto; smt().
auto; smt().
hoare.
call (_ : true); auto; smt().
smt().
hoare.
call (_ : true); auto; smt().
smt().
auto; smt().
qed.

local lemma H2'_main_ll :
  forall (O <: BRO.BOR{H2'}),
  islossless O.adv_bhash => islossless O.adv_within_budget =>
  islossless O.server_bhash => islossless O.client_bhash =>
  islossless O.hash =>
  islossless H2'(O).main.
proof.
move =>
  O adv_bhash_ll adv_within_budget_ll server_bhash_ll client_bhash_ll
  hash_ll.
proc.
call (_ : true ==> true).
apply (final_ll (BOrToCOr(O))); apply hash_ll.
seq 5 : (H2'.qrys_ctr = 0).
call (_ : true).
proc; call (_ : true); auto.
auto.
call (_ : true ==> true).
apply (init_and_get_db_ll (BOrToCOr(O))); proc; call adv_bhash_ll; auto.
auto; progress; apply sec_distr_ll.
if.
seq 1 : (H2'.qrys_ctr = 0 /\ db_opt <> None).
call (_ : true); auto.
call adv_within_budget_ll; auto.
if.
call (_ : H2'.qrys_ctr <= qrys_max ==> true).
apply (H2'_client_loop_ll O);
  [apply adv_bhash_ll | apply adv_within_budget_ll |
   apply server_bhash_ll | apply client_bhash_ll |
   apply hash_ll].
call (_ : true ==> true).
apply (H2'_server_count_and_hash_db_ll O); apply server_bhash_ll.
auto; progress; apply qrys_max_ge0.
auto.
hoare; call (_ : true); auto.
trivial.
auto.
hoare.
call (_ : true).
proc; call (_ : true); auto.
auto.
trivial.
qed.

(* now we apply the Switching Lemma to H2' *)

local lemma GSwitching_H2' &m :
  `|Pr[BRO.GSwitching(H2', BRO.BOr).main() @ &m : res] -
    Pr[BRO.GSwitching(H2', BRO.BOrInj).main() @ &m : res]| <=
  BRO.coll_bound.
proof.
apply (BRO.Switching H2' &m).
move => O; apply (H2'_main_ll O).
qed.

local lemma G3_GSwitching_H2'_BOrInj_main &m :
  equiv
  [G3.main ~ BRO.GSwitching(H2', BRO.BOrInj).main :
   true ==> ={res}].
proof.
proc.
inline BRO.GSwitching(H2', BRO.BOrInj).SA.main.
swap{1} 4 -3; sim.
qed.

local lemma G3_GSwitching_H2'_BOrInj &m :
  Pr[G3.main() @ &m : res] =
  Pr[BRO.GSwitching(H2', BRO.BOrInj).main() @ &m : res].
proof. by byequiv (G3_GSwitching_H2'_BOrInj_main &m). qed.

local lemma GSwitching_H2'_BOr_G4_main &m :
  equiv
  [BRO.GSwitching(H2', BRO.BOr).main ~ G4.main:
   true ==> ={res}].
proof.
proc.
inline BRO.GSwitching(H2', BRO.BOr).SA.main.
swap{2} 4 -3; sim.
qed.

local lemma GSwitching_H2'_BOr_G4 &m :
  Pr[BRO.GSwitching(H2', BRO.BOr).main() @ &m : res] =
  Pr[G4.main() @ &m : res].
proof. by byequiv (GSwitching_H2'_BOr_G4_main &m). qed.

local lemma G3_G4 &m :
  `|Pr[G3.main() @ &m : res] - Pr[G4.main() @ &m : res]| <=
  BRO.coll_bound.
proof.
have -> :
  `|Pr[G3.main() @ &m : res] - Pr[G4.main() @ &m : res]| =
  `|Pr[G4.main() @ &m : res] - Pr[G3.main() @ &m : res]|
  by rewrite RealOrder.distrC.
rewrite (G3_GSwitching_H2'_BOrInj &m) -(GSwitching_H2'_BOr_G4 &m)
        (GSwitching_H2' &m).
qed.

(* now we use the Triangular Inequality to show the relationship
   between GReal(Adv) and G4: *)

local lemma GReal_G4 &m :
  `|Pr[GReal(Adv).main() @ &m : res] - Pr[G4.main() @ &m : res]| <=
   2%r * BRO.coll_bound.
proof.
have GReal_G3 :
  `|Pr[GReal(Adv).main() @ &m : res] - Pr[G3.main() @ &m : res]| <=
  BRO.coll_bound
  by apply (GReal_G3 &m).
have G3_G4 :
  `|Pr[G3.main() @ &m : res] - Pr[G4.main() @ &m : res]| <=
  BRO.coll_bound
  by apply (G3_G4 &m).
rewrite
  (RealOrder.ler_trans 
   (`|Pr[GReal(Adv).main() @ &m : res] - Pr[G3.main() @ &m : res]| +
    `|Pr[G3.main() @ &m : res] - Pr[G4.main() @ &m : res]|))
   1:RealOrder.ler_dist_add.
have -> :
  2%r * BRO.coll_bound = BRO.coll_bound + BRO.coll_bound
  by smt().
by rewrite RealOrder.ler_add 1:GReal_G3 G3_G4.
qed.

(* in G5, we switch back to using RO.Or (instead of BRO.BOr), with
   Adversary being given counted random oracle view of RO.Or *)

local module G5 = {
  module Or  = RO.Or
  module COr = CRO.COr(Or)
  module A   = Adv(COr)

  var cv : client_view
  var sec : sec
  var elems_cnts : elems_counts
  var qrys_ctr : int

  proc server_count_and_hash_db(db : db) : unit = {
    var i : int; var elem : elem;
    db <- Shuffle.shuffle(db);
    elems_cnts <- empty_ec; i <- 0;
    while (i < size db) {
      elem <- nth elem_default db i;
      elems_cnts <- incr_count elems_cnts elem;
      Or.hash((elem, sec));  (* redundant *)
      i <- i + 1;
    }
  }

  proc tp_count_elem(attr : elem) : int = {
    return get_count elems_cnts attr;
  }

  proc client_loop() : unit = {
    var cnt : int; var tag : tag; var qry_opt : elem option;
    var adv_within_budg : bool;
    var not_done : bool <- true;
    while (not_done) {
      qry_opt <@ A.get_qry(cv);
      if (qry_opt = None) {
        not_done <- false;
        cv <- cv ++ [cv_got_qry None];
      }
      else {
        adv_within_budg <@ COr.within_budget();
        if (qrys_ctr < qrys_max /\ adv_within_budg) {
          cv <- cv ++ [cv_got_qry qry_opt];
          qrys_ctr <- qrys_ctr + 1;
          tag <@ Or.hash((oget qry_opt, sec));
          cnt <@ tp_count_elem(oget qry_opt);
          cv <- cv ++ [cv_query_count(oget qry_opt, tag, cnt)];
          A.qry_done(cv);
        }
        else {
          not_done <- false;
          cv <- cv ++ [cv_got_qry None];
        }
      }
    }
  }

  proc main() : bool = {
    var db_opt : db option;
    var b : bool;
    var adv_within_budg : bool;
    sec <$ sec_distr;
    cv <- [cv_got_sec sec];
    qrys_ctr <- 0;
    Or.init(); COr.init();
    db_opt <@ A.init_and_get_db(cv);
    if (db_opt <> None) {
      adv_within_budg <@ COr.within_budget();
      if (num_uniqs (oget db_opt) <= db_uniqs_max /\ adv_within_budg) {
        server_count_and_hash_db(oget db_opt);
        client_loop();
      }
    }
    b <@ A.final(cv);
    return b;
  }
}.

local lemma G4_G5_server_count_and_hash_db :
  equiv
  [G4.server_count_and_hash_db ~ G5.server_count_and_hash_db :
   ={db} /\ ={mp}(BRO.BOr, RO.Or) /\ ={sec}(G4, G5) ==>
   ={elems_cnts}(G4, G5) /\ ={mp}(BRO.BOr, RO.Or)].
proof.
proc.
seq 3 3 :
  (={db, i} /\ ={sec, elems_cnts}(G4, G5) /\ ={mp}(BRO.BOr, RO.Or));
  first sim.
while (={db, i} /\ ={sec, elems_cnts}(G4, G5) /\ ={mp}(BRO.BOr, RO.Or)).
wp.
call
  (_  :
   ={inp} /\ ={sec}(G4, G5) /\ ={mp}(BRO.BOr, RO.Or) ==>
   ={res} /\ ={mp}(BRO.BOr, RO.Or)).
by symmetry; conseq Or_hash_BOr_server_bhash.
auto.
auto.
qed.

local lemma G4_G5_client_loop :
  equiv
  [G4.client_loop ~ G5.client_loop :
   ={glob Adv} /\ ={mp}(BRO.BOr, RO.Or) /\
   BRO.BOr.adv_inps{1} = CRO.COr.inps{2} /\
   BRO.BOr.adv_ctr{1} = CRO.COr.ctr{2} /\
   BRO.BOr.adv_over{1} = CRO.COr.over{2} /\
   ={sec, elems_cnts, cv, qrys_ctr}(G4, G5) ==>
   ={glob Adv} /\ ={mp}(BRO.BOr, RO.Or) /\
   BRO.BOr.adv_inps{1} = CRO.COr.inps{2} /\
   BRO.BOr.adv_ctr{1} = CRO.COr.ctr{2} /\
   BRO.BOr.adv_over{1} = CRO.COr.over{2} /\
   ={sec, elems_cnts, cv, qrys_ctr}(G4, G5)].
proof.
proc.
sp.
while
  (={not_done, glob Adv} /\ ={mp}(BRO.BOr, RO.Or) /\
   BRO.BOr.adv_inps{1} = CRO.COr.inps{2} /\
   BRO.BOr.adv_ctr{1} = CRO.COr.ctr{2} /\
   BRO.BOr.adv_over{1} = CRO.COr.over{2} /\
   ={sec, elems_cnts, cv, qrys_ctr}(G4, G5)).
seq 1 1 :
  (={not_done, qry_opt, glob Adv} /\ ={mp}(BRO.BOr, RO.Or) /\
   BRO.BOr.adv_inps{1} = CRO.COr.inps{2} /\
   BRO.BOr.adv_ctr{1} = CRO.COr.ctr{2} /\
   BRO.BOr.adv_over{1} = CRO.COr.over{2} /\
   ={sec, elems_cnts, cv, qrys_ctr}(G4, G5)).
call
  (_ :
   ={mp}(BRO.BOr, RO.Or) /\
   BRO.BOr.adv_inps{1} = CRO.COr.inps{2} /\
   BRO.BOr.adv_ctr{1} = CRO.COr.ctr{2} /\
   BRO.BOr.adv_over{1} = CRO.COr.over{2}).
by symmetry; conseq COr_Or_BOrToCOr_BOr_chash.
auto.
if => //.
auto.
inline BRO.BOr.adv_within_budget G5.COr.within_budget; sp.
if => //.
call
  (_ :
   ={mp}(BRO.BOr, RO.Or) /\
   BRO.BOr.adv_inps{1} = CRO.COr.inps{2} /\
   BRO.BOr.adv_ctr{1} = CRO.COr.ctr{2} /\
   BRO.BOr.adv_over{1} = CRO.COr.over{2}).
by symmetry; conseq COr_Or_BOrToCOr_BOr_chash.
wp.
call (_ : ={elems_cnts}(G4, G5)); auto.
call
  (_ :
   ={inp} /\ ={mp}(BRO.BOr, RO.Or) ==>
   ={res} /\ ={mp}(BRO.BOr, RO.Or)).
by symmetry; conseq Or_hash_BOr_client_bhash.
auto.
auto.
auto.
qed.

local lemma G4_G5_main :
  equiv[G4.main ~ G5.main : true ==> ={res}].
proof.
proc.
seq 4 5 :
  (={mp}(BRO.BOr, RO.Or) /\
   BRO.BOr.adv_inps{1} = CRO.COr.inps{2} /\
   BRO.BOr.adv_ctr{1} = CRO.COr.ctr{2} /\
   BRO.BOr.adv_over{1} = CRO.COr.over{2} /\
   ={sec, cv, qrys_ctr}(G4, G5));
  first inline *; auto.
seq 1 1 :
  (={db_opt, glob Adv} /\ ={mp}(BRO.BOr, RO.Or) /\
   BRO.BOr.adv_inps{1} = CRO.COr.inps{2} /\
   BRO.BOr.adv_ctr{1} = CRO.COr.ctr{2} /\
   BRO.BOr.adv_over{1} = CRO.COr.over{2} /\
   ={sec, cv, qrys_ctr}(G4, G5)).
call
  (_ :
   ={mp}(BRO.BOr, RO.Or) /\
   BRO.BOr.adv_inps{1} = CRO.COr.inps{2} /\
   BRO.BOr.adv_ctr{1} = CRO.COr.ctr{2} /\
   BRO.BOr.adv_over{1} = CRO.COr.over{2}).
by symmetry; conseq COr_Or_BOrToCOr_BOr_chash.
auto.
call (_ : ={mp}(BRO.BOr, RO.Or)).
by symmetry; conseq COr_Or_BOrToCOr_BOr_hash.
if => //.
inline BRO.BOr.adv_within_budget G5.COr.within_budget; sp.
if => //.
call G4_G5_client_loop.
call G4_G5_server_count_and_hash_db.
auto.
qed.

local lemma G4_G5 &m :
  Pr[G4.main() @ &m : res] = Pr[G5.main() @ &m : res].
proof. by byequiv G4_G5_main. qed.

local lemma GReal_G5 &m :
  `|Pr[GReal(Adv).main() @ &m : res] - Pr[G5.main() @ &m : res]| <=
   2%r * BRO.coll_bound.
proof. rewrite -(G4_G5 &m) (GReal_G4 &m). qed.

(* in G6, we get rid of the Server's hashing, which is now redundant,
   changing the Server's procedure name to reflect this *)

local module G6 = {
  module Or  = RO.Or
  module COr = CRO.COr(Or)
  module A   = Adv(COr)

  var cv : client_view
  var sec : sec
  var elems_cnts : elems_counts
  var qrys_ctr : int

  proc server_count_db(db : db) : unit = {
    var i : int; var elem : elem;
    db <- Shuffle.shuffle(db);
    elems_cnts <- empty_ec; i <- 0;
    while (i < size db) {
      elem <- nth elem_default db i;
      elems_cnts <- incr_count elems_cnts elem;
      (* redundant hashing removed *)
      i <- i + 1;
    }
  }

  proc tp_count_elem(attr : elem) : int = {
    return get_count elems_cnts attr;
  }

  proc client_loop() : unit = {
    var cnt : int; var tag : tag; var qry_opt : elem option;
    var adv_within_budg : bool;
    var not_done : bool <- true;
    while (not_done) {
      qry_opt <@ A.get_qry(cv);
      if (qry_opt = None) {
        not_done <- false;
        cv <- cv ++ [cv_got_qry None];
      }
      else {
        adv_within_budg <@ COr.within_budget();
        if (qrys_ctr < qrys_max /\ adv_within_budg) {
          cv <- cv ++ [cv_got_qry qry_opt];
          qrys_ctr <- qrys_ctr + 1;
          tag <@ Or.hash((oget qry_opt, sec));
          cnt <@ tp_count_elem(oget qry_opt);
          cv <- cv ++ [cv_query_count(oget qry_opt, tag, cnt)];
          A.qry_done(cv);
        }
        else {
          not_done <- false;
          cv <- cv ++ [cv_got_qry None];
        }
      }
    }
  }

  proc main() : bool = {
    var db_opt : db option;
    var b : bool;
    var adv_within_budg : bool;
    sec <$ sec_distr;
    cv <- [cv_got_sec sec];
    qrys_ctr <- 0;
    Or.init(); COr.init();
    db_opt <@ A.init_and_get_db(cv);
    if (db_opt <> None) {
      adv_within_budg <@ COr.within_budget();
      if (num_uniqs (oget db_opt) <= db_uniqs_max /\ adv_within_budg) {
        server_count_db(oget db_opt);
        client_loop();
      }
    }
    b <@ A.final(cv);
    return b;
  }
}.

local clone RO.RedundantHashing as RH
proof *.
(* nothing to prove *)

local module HashingToOr(Hashing : RH.HASHING) : RO.OR = {
  proc init() : unit = { }

  proc hash = Hashing.hash
}.

local module (HashingAdv : RH.HASHING_ADV) (Hashing : RH.HASHING) = {
  module COr = CRO.COr(HashingToOr(Hashing))
  module A   = Adv(COr)

  var cv : client_view
  var sec : sec
  var elems_cnts : elems_counts
  var qrys_ctr : int

  proc server_count_and_hash_db(db : db) : unit = {
    var i : int; var elem : elem;
    db <- Shuffle.shuffle(db);
    elems_cnts <- empty_ec; i <- 0;
    while (i < size db) {
      elem <- nth elem_default db i;
      elems_cnts <- incr_count elems_cnts elem;
      Hashing.rhash((elem, sec));  (* redundant *)
      i <- i + 1;
    }
  }

  proc tp_count_elem(attr : elem) : int = {
    return get_count elems_cnts attr;
  }

  proc client_loop() : unit = {
    var cnt : int; var tag : tag; var qry_opt : elem option;
    var adv_within_budg : bool;
    var not_done : bool <- true;
    while (not_done) {
      qry_opt <@ A.get_qry(cv);
      if (qry_opt = None) {
        not_done <- false;
        cv <- cv ++ [cv_got_qry None];
      }
      else {
        adv_within_budg <@ COr.within_budget();
        if (qrys_ctr < qrys_max /\ adv_within_budg) {
          cv <- cv ++ [cv_got_qry qry_opt];
          qrys_ctr <- qrys_ctr + 1;
          tag <@ Hashing.hash((oget qry_opt, sec));
          cnt <@ tp_count_elem(oget qry_opt);
          cv <- cv ++ [cv_query_count(oget qry_opt, tag, cnt)];
          A.qry_done(cv);
        }
        else {
          not_done <- false;
          cv <- cv ++ [cv_got_qry None];
        }
      }
    }
  }

  proc main() : bool = {
    var db_opt : db option;
    var b : bool;
    var adv_within_budg : bool;
    (* needed for using RH.GNonOptHashing_GOptHashing: *)
    elems_cnts <- empty_ec;
    sec <$ sec_distr;
    cv <- [cv_got_sec sec];
    qrys_ctr <- 0;
    COr.init();
    db_opt <@ A.init_and_get_db(cv);
    if (db_opt <> None) {
      adv_within_budg <@ COr.within_budget();
      if (num_uniqs (oget db_opt) <= db_uniqs_max /\ adv_within_budg) {
        server_count_and_hash_db(oget db_opt);
        client_loop();
      }
    }
    b <@ A.final(cv);
    return b;
  }
}.

local lemma G5_HashingAdv_NonOptHashing_server_count_and_hash_db :
  equiv
  [G5.server_count_and_hash_db ~
   HashingAdv(RH.NonOptHashing(RO.Or)).server_count_and_hash_db :
   ={db, glob RO.Or, glob Adv} /\ ={sec}(G5, HashingAdv) ==>
   ={glob RO.Or} /\ ={elems_cnts}(G5, HashingAdv)].
proof.
proc.
inline RH.NonOptHashing(RO.Or).rhash.
seq 3 3 :
  (={db, glob RO.Or, glob Adv, i} /\ ={sec, elems_cnts}(G5, HashingAdv));
  first sim.
while
  (={db, glob RO.Or, glob Adv, i} /\ ={sec, elems_cnts}(G5, HashingAdv)).
wp.
call (_ : ={RO.Or.mp}); first  sim.
auto.
auto.
qed.

local lemma G5_HashingAdv_NonOptHashing_client_loop :
  equiv
  [G5.client_loop ~ HashingAdv(RH.NonOptHashing(RO.Or)).client_loop :
   ={glob RO.Or, glob CRO.COr, glob Adv} /\
   ={sec, cv, qrys_ctr, elems_cnts}(G5, HashingAdv) ==>
   ={glob RO.Or, glob CRO.COr, glob Adv} /\
   ={cv, qrys_ctr}(G5, HashingAdv)].
proof. sim. qed.

local lemma G5_GNonOptHashing_HashingAdv_main :
  equiv
  [G5.main ~ RH.GNonOptHashing(HashingAdv).main :
   true ==> ={res}].
proof.
proc; inline RH.GNonOptHashing(HashingAdv).HA.main.
swap{1} [4..5] -2; swap{2} 2 5; swap{2} 2 -1; swap{2} 5 -2.
seq 5 5 :
  (={glob RO.Or, glob CRO.COr} /\
   ={sec, cv, qrys_ctr}(G5, HashingAdv));
  first inline*; auto.
seq 1 1 :
  (={db_opt, glob RO.Or, glob CRO.COr, glob Adv} /\
   ={sec, cv, qrys_ctr}(G5, HashingAdv)); first sim.
sp; wp.
call (_ : ={glob RO.Or, glob CRO.COr}); first sim.
if => //.
inline
  G5.COr.within_budget
  HashingAdv(RH.NonOptHashing(RO.Or)).COr.within_budget; sp.
if => //.
call G5_HashingAdv_NonOptHashing_client_loop.
call G5_HashingAdv_NonOptHashing_server_count_and_hash_db.
auto.
qed.

local lemma G5_GNonOptHashing_HashingAdv &m :
  Pr[G5.main() @ &m : res] =
  Pr[RH.GNonOptHashing(HashingAdv).main() @ &m : res].
proof. by byequiv G5_GNonOptHashing_HashingAdv_main. qed.

local lemma
  HashingAdv_OptHashing_server_count_and_hash_db_G6_server_count_db :
  equiv
  [HashingAdv(RH.OptHashing(RO.Or)).server_count_and_hash_db ~
   G6.server_count_db :
   ={db, glob RO.Or, glob Adv} /\ ={sec}(HashingAdv, G6) ==>
   ={glob RO.Or} /\ ={elems_cnts}(HashingAdv, G6)].
proof.
proc; inline RH.OptHashing(RO.Or).rhash; sim.
qed.

local lemma HashingAdv_OptHashing_G6_client_loop :
  equiv
  [HashingAdv(RH.OptHashing(RO.Or)).client_loop ~ G6.client_loop :
   ={glob RO.Or, glob CRO.COr, glob Adv} /\
   ={sec, cv, qrys_ctr, elems_cnts}(HashingAdv, G6) ==>
   ={glob RO.Or, glob CRO.COr, glob Adv} /\
   ={cv, qrys_ctr}(HashingAdv, G6)].
proof. sim. qed.

local lemma GOptHashing_HashingAdv_G6_main :
  equiv
  [RH.GOptHashing(HashingAdv).main ~ G6.main :
   true ==> ={res}].
proof.
proc; inline RH.GOptHashing(HashingAdv).HA.main.
swap{1} 2 5; swap{1} 2 -1; swap{1} 5 -2; swap{2} [4..5] -2.
seq 5 5 :
  (={glob RO.Or, glob CRO.COr} /\
   ={sec, cv, qrys_ctr}(HashingAdv, G6));
  first inline*; auto.
seq 1 1 :
  (={db_opt, glob RO.Or, glob CRO.COr, glob Adv} /\
   ={sec, cv, qrys_ctr}(HashingAdv, G6)); first sim.
sp; wp.
call (_ : ={glob RO.Or, glob CRO.COr}); first sim.
if => //.
inline
  HashingAdv(RH.OptHashing(RO.Or)).COr.within_budget
  G6.COr.within_budget; sp.
if => //.
call HashingAdv_OptHashing_G6_client_loop.
call HashingAdv_OptHashing_server_count_and_hash_db_G6_server_count_db.
auto.
qed.

local lemma GOptHashing_HashingAdv_G6 &m :
  Pr[RH.GOptHashing(HashingAdv).main() @ &m : res] =
  Pr[G6.main() @ &m : res].
proof. by byequiv GOptHashing_HashingAdv_G6_main. qed.

local lemma G5_G6 &m :
  Pr[G5.main() @ &m : res] = Pr[G6.main() @ &m : res].
proof.
by rewrite (G5_GNonOptHashing_HashingAdv &m)
           (RH.GNonOptHashing_GOptHashing HashingAdv &m)
           (GOptHashing_HashingAdv_G6 &m).
qed.

local lemma GReal_G6 &m :
  `|Pr[GReal(Adv).main() @ &m : res] - Pr[G6.main() @ &m : res]| <=
   2%r * BRO.coll_bound.
proof. rewrite -(G5_G6 &m) (GReal_G5 &m). qed.

(* in G7, we no longer randomly shuffle the database in
   server_count *)

local module G7 = {
  module Or  = RO.Or
  module COr = CRO.COr(Or)
  module A   = Adv(COr)

  var cv : client_view
  var sec : sec
  var elems_cnts : elems_counts
  var qrys_ctr : int

  proc server_count_db(db : db) : unit = {
    var i : int;
    var elem : elem;
    (* database shuffling removed *)
    elems_cnts <- empty_ec; i <- 0;
    while (i < size db) {
      elem <- nth elem_default db i;
      elems_cnts <- incr_count elems_cnts elem;
      i <- i + 1;
    }
  }

  proc tp_count_elem(attr : elem) : int = {
    return get_count elems_cnts attr;
  }

  proc client_loop() : unit = {
    var cnt : int;
    var tag : tag;
    var qry_opt : elem option;
    var adv_within_budg : bool;
    var not_done : bool <- true;
    while (not_done) {
      qry_opt <@ A.get_qry(cv);
      if (qry_opt = None) {
        not_done <- false;
        cv <- cv ++ [cv_got_qry None];
      }
      else {
        adv_within_budg <@ COr.within_budget();
        if (qrys_ctr < qrys_max /\ adv_within_budg) {
          cv <- cv ++ [cv_got_qry qry_opt];
          qrys_ctr <- qrys_ctr + 1;
          tag <@ Or.hash((oget qry_opt, sec));
          cnt <@ tp_count_elem(oget qry_opt);
          cv <- cv ++ [cv_query_count(oget qry_opt, tag, cnt)];
          A.qry_done(cv);
        }
        else {
          not_done <- false;
          cv <- cv ++ [cv_got_qry None];
        }
      }
    }
  }

  proc main() : bool = {
    var db_opt : db option;
    var b : bool;
    var adv_within_budg : bool;
    sec <$ sec_distr;
    cv <- [cv_got_sec sec];
    qrys_ctr <- 0;
    Or.init(); COr.init();
    db_opt <@ A.init_and_get_db(cv);
    if (db_opt <> None) {
      adv_within_budg <@ COr.within_budget();
      if (num_uniqs (oget db_opt) <= db_uniqs_max /\ adv_within_budg) {
        server_count_db(oget db_opt);
        client_loop();
      }
    }
    b <@ A.final(cv);
    return b;
  }
}.

(* we'll make use of IterProc to show that computing a database's
   elements counts map works out the same no matter whether
   the database is first shuffled or not *)

local clone include IterProc with type t <- elem
proof *.
(* nothing to realize *)

(* I.f(elem) updates the elements counts map of G6 to take account
   of elem *)

local module I = {
  proc f (elem : elem) = {
    G6.elems_cnts <- incr_count G6.elems_cnts elem;
  }
}.

local lemma iter_perm2 :
  equiv
  [Iter(I).iter_12 ~ Iter(I).iter_21 :
   ={glob I, t1, t2} ==> ={glob I}].
proof.
proc; inline*; auto => |> &2; apply incr_count_swap.
qed.

local lemma G6_G7_server_count_db :
  equiv
  [G6.server_count_db ~ G7.server_count_db :
   ={db} ==> ={elems_cnts}(G6, G7)].
proof.
proc.
seq 1 0 : (perm_eq db{1} db{2}).
exists* db{2}; elim* => db'.
call{1} (Shuffle_shuffle_perm_phoare db').
auto.
sp.
transitivity{1}
  { Iter(I).iter(db); }
  (={db, G6.elems_cnts} /\ i{1} = 0 ==> ={G6.elems_cnts})
  (perm_eq db{1} db{2} /\
   ={elems_cnts}(G6,G7) /\ i{2} = 0 ==>
   ={elems_cnts}(G6,G7)) => //.
progress; by exists empty_ec db{1}.
inline Iter(I).iter I.f; sp.
while
  (={G6.elems_cnts} /\ 0 <= i{1} <= size db{1} /\
   drop i{1} db{1} = l{2}).
auto => |> &1 &2 ge0_i _ lt_i_sz_db drop_i_db_ne_nil.
split. split.
have -> // : nth elem_default db{1} i{1} = head witness (drop i{1} db{1}).
rewrite -{1}(cat_take_drop i{1} db{1}) nth_cat.
have i_eq_sz_tak_i_db : i{1} = size (take i{1} db{1}) by smt(size_take).
have -> /= : (i{1} < size (take i{1} db{1})) = false by smt().
have -> : i{1} - size (take i{1} db{1}) = 0 by smt().
rewrite (nth_in_range 0 elem_default witness); first smt(size_eq0 size_ge0).
by rewrite nth_head.
split; first smt().
by rewrite -drop_drop // addzC.
split.
move => i_add1_lt_sz_db; smt(size_drop).
rewrite -drop_drop // => drop_i_add1_db_ne_nil.
have sz_drop_i_add1_db := (size_drop (1 + i{1}) db{1} _); first smt().
rewrite IntOrder.ler_maxr 1:/# in sz_drop_i_add1_db.
smt(size_eq0).
auto => |> &2. split.
split; [apply size_ge0 | by rewrite drop0].
split; smt(size_ge0 size_eq0).
transitivity{1}
  { Iter(I).iter(db); }
  (perm_eq db{1} db{2} /\ ={G6.elems_cnts} /\ i{2} = 0 ==>
   ={G6.elems_cnts})
  (={elems_cnts}(G6, G7) /\ ={db} /\ i{2} = 0 ==>
   ={elems_cnts}(G6, G7)) => //.
progress; by exists G7.elems_cnts{2} db{2} 0.
call (iter_perm I iter_perm2).
auto.
inline Iter(I).iter I.f; sp.
while
  (={elems_cnts}(G6, G7) /\ 0 <= i{2} <= size db{2} /\
   drop i{2} db{2} = l{1}).
auto => |> &1 ge0_i _ drop_i_db_ne_nil lt_i_sz_db.
split. split.
have -> // : nth elem_default db{1} i{1} = head witness (drop i{1} db{1}).
rewrite -{1}(cat_take_drop i{1} db{1}) nth_cat.
have i_eq_sz_tak_i_db : i{1} = size (take i{1} db{1}) by smt(size_take).
have -> /= : (i{1} < size (take i{1} db{1})) = false by smt().
have -> : i{1} - size (take i{1} db{1}) = 0 by smt().
rewrite (nth_in_range 0 elem_default witness); first smt(size_eq0 size_ge0).
by rewrite nth_head.
split; first smt().
by rewrite -drop_drop // addzC.
split.
rewrite -drop_drop // => drop_i_add1_db_ne_nil.
have sz_drop_i_add1_db := (size_drop (1 + i{1}) db{1} _); first smt().
rewrite IntOrder.ler_maxr 1:/# in sz_drop_i_add1_db.
smt(size_eq0).
move => i_add1_lt_sz_db; smt(size_drop).
auto => |> &2. split.
split; [apply size_ge0 | by rewrite drop0].
split; smt(size_ge0 size_eq0).
qed.

local lemma G6_G7_main :
  equiv[G6.main ~ G7.main : true ==> ={res}].
proof.
proc.
seq 6 6 :
  (={db_opt, glob RO.Or, glob CRO.COr, glob Adv} /\
   ={sec, cv, qrys_ctr}(G6, G7));
  first inline *; sim.
call (_ : ={glob RO.Or}); first sim.
if => //.
inline G6.COr.within_budget G7.COr.within_budget; sp.
if => //.
call
  (_ : 
   ={glob RO.Or, glob CRO.COr, glob Adv} /\
   ={sec, cv, qrys_ctr, elems_cnts}(G6, G7)); first sim.
call G6_G7_server_count_db.
auto.
qed.

local lemma G6_G7 &m :
  Pr[G6.main() @ &m : res] = Pr[G7.main() @ &m : res].
proof. by byequiv G6_G7_main. qed.

local lemma GReal_G7 &m :
  `|Pr[GReal(Adv).main() @ &m : res] - Pr[G7.main() @ &m : res]| <=
   2%r * BRO.coll_bound.
proof. rewrite -(G6_G7 &m) (GReal_G6 &m). qed.

(* now we are ready to connect G7 and GIdeal(Adv, Sim) *)

local lemma G7_server_count_db_GIdeal_count_db :
  equiv
  [G7.server_count_db ~ GIdeal(Adv, Sim).count_db :
   ={db} ==>
   G7.elems_cnts{1} = GIdeal.db_elems_cnts{2}].
proof. sim. qed.

local lemma G7_GIdeal_client_loop :
  equiv
  [G7.client_loop ~ GIdeal(Adv, Sim).S.client_loop :
   ={glob RO.Or, glob CRO.COr, glob Adv} /\
   ={sec, cv}(G7, Sim) /\ ={qrys_ctr}(G7, GIdeal) /\
   G7.elems_cnts{1} = GIdeal.db_elems_cnts{2} ==>
   ={glob RO.Or, glob CRO.COr, glob Adv} /\
   ={cv}(G7, Sim)].
proof.
proc.
inline GIdeal(Adv, Sim).SIG.get_qry_count
       GIdeal(Adv, Sim).SIG.qry_done
       G7.tp_count_elem.
while
  (={not_done} /\ ={glob RO.Or, glob CRO.COr, glob Adv} /\
   ={sec, cv}(G7, Sim) /\ ={qrys_ctr}(G7, GIdeal) /\
   G7.elems_cnts{1} = GIdeal.db_elems_cnts{2}).
seq 1 2 :
  (={not_done, qry_opt} /\ ={glob RO.Or, glob CRO.COr, glob Adv} /\
   ={sec, cv}(G7, Sim) /\ ={qrys_ctr}(G7, GIdeal) /\
   G7.elems_cnts{1} = GIdeal.db_elems_cnts{2}); first sim.
if => //.
rcondt{2} 3; auto.
inline G7.COr.within_budget GIdeal(Adv, Sim).COr.within_budget.
seq 1 1 :
  (={not_done, qry_opt, adv_within_budg} /\
   ={glob RO.Or, glob CRO.COr, glob Adv} /\
   ={sec, cv}(G7, Sim) /\ ={qrys_ctr}(G7, GIdeal) /\
   G7.elems_cnts{1} = GIdeal.db_elems_cnts{2} /\
   qry_opt{1} <> None); first auto.
if => //.
rcondf{2} 5; first auto.
call (_ : ={glob RO.Or, glob CRO.COr}); first sim.
wp.
call (_ : ={glob RO.Or}); first sim.
auto; progress; congr; congr; congr;
  by rewrite some_oget.
rcondt{2} 3; first auto.
auto.
auto.
qed.

local lemma G7_GIdeal_main :
  equiv[G7.main ~ GIdeal(Adv, Sim).main : true ==> ={res}].
proof.        
proc.
inline GIdeal(Adv, Sim).S.init
       GIdeal(Adv, Sim).S.get_view
       G7.COr.within_budget
       GIdeal(Adv, Sim).COr.within_budget.
seq 5 5 :
  (={glob RO.Or, glob CRO.COr} /\ ={sec, cv}(G7, Sim) /\
   ={qrys_ctr}(G7, GIdeal)).
swap{1} 3 -2; sim.
seq 1 2 :
  (={db_opt, glob RO.Or, glob CRO.COr, glob Adv} /\
   ={sec, cv}(G7, Sim) /\ ={qrys_ctr}(G7, GIdeal)); first sim.
call (_ : ={glob RO.Or}); first sim.
wp.
if => //.
sp.
if => //.
call G7_GIdeal_client_loop.
call G7_server_count_db_GIdeal_count_db.
auto.
qed.

local lemma G7_GIdeal &m :
  Pr[G7.main() @ &m : res] = Pr[GIdeal(Adv, Sim).main() @ &m : res].
proof. by byequiv G7_GIdeal_main. qed.

lemma GReal_GIdeal' &m :
  `|Pr[GReal(Adv).main() @ &m : res] -
    Pr[GIdeal(Adv, Sim).main() @ &m : res]| <=
  (budget * (budget - 1))%r / (2 ^ tag_len)%r.
proof.
rewrite -(G7_GIdeal &m).
have -> :
  (budget * (budget - 1))%r / (2 ^ tag_len)%r = 2%r * BRO.coll_bound
    by rewrite /BRO.coll_bound Ring.IntID.exprS 1:tag_len_ge0
               (fromintM 2) invfM mulrA (mulrC 2%r) -mulrA
               (mulrA 2%r) divrr.
apply (GReal_G7 &m).
qed.

end section.

(* main theorem *)

lemma GReal_GIdeal :
  exists (Sim <: SIM{GReal, GIdeal}),
  forall (Adv <: ADV{GReal, GIdeal, Sim}) &m,
  (forall (O <: CRO.COR{Adv}),
   islossless O.chash => islossless Adv(O).init_and_get_db) =>
  (forall (O <: CRO.COR{Adv}),
   islossless O.chash => islossless Adv(O).get_qry) =>
  (forall (O <: CRO.COR{Adv}),
   islossless O.chash => islossless Adv(O).qry_done) =>
  (forall (O <: CRO.COR{Adv}),
   islossless O.hash => islossless Adv(O).final) =>
  `|Pr[GReal(Adv).main() @ &m : res] -
    Pr[GIdeal(Adv, Sim).main() @ &m : res]| <=
  (budget * (budget - 1))%r / (2 ^ tag_len)%r.
proof.
exists Sim =>
  Adv &m init_and_get_db_ll get_qry_ll qry_done_ll final_ll.
apply
  (GReal_GIdeal' Adv init_and_get_db_ll get_qry_ll qry_done_ll
   final_ll &m).
qed.
