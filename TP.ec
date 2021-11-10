(* TP.ec *)

(* Proof of Security Against TP (Third Party) *)

prover quorum=2 ["Alt-Ergo" "Z3"].  (* both Alt-Ergo and Z3 must succeed *)

(************* PCR Protocol and Supporting Definitions and Lemmas *************)

require import Protocol.

(*************************** Private Random Oracle ****************************)

(* private random oracle for hashing elements (not element/secret pairs) *)

clone RandomOracle as Priv with
  type input <- elem,
  op output_len <- tag_len,
  type output <- tag,
  op output_default <- zeros_tag,
  op output_distr <- tag_distr
proof *.
(* beginning of realization *)
realize output_len_ge0. apply tag_len_ge0. qed.

realize mu1_output_distr. apply mu1_tag_distr. qed.

realize output_distr_ll. apply tag_distr_ll. qed.
(* end of realization *)

(********************************* Adversary **********************************)

(* Adversary's hashing limit *)

op limit : int.

axiom limit_ge0 : 0 <= limit.

(* limited random oracle *)

clone RO.Limited as LRO with
  op limit <- limit
proof *.
(* beginning of realization *)
realize limit_ge0. apply limit_ge0. qed.
(* end of realization *)

(* maximum number of queries that may be made by Adversary *)

op qrys_max : int.

axiom qrys_max_ge0 : 0 <= qrys_max.

(* Adversary module type, parameterized by a random oracle *)

module type ADV(O : RO.OR) = {
  (* all procedures are supplied the current TP view; and all
     procedures can only call O.hash (not O.init) *)

  (* initialize Adversary, and try to get a database from it; None
     means refusal *)

  proc * init_and_get_db(tpv : tp_view) : db option {O.hash}

  (* try to get a query from Adversary; None means done supplying queries *)

  proc get_qry(tpv : tp_view) : elem option {O.hash}

  (* tell the Adversary that done processing its last query *)

  proc qry_done(tpv : tp_view) : unit {O.hash}

  (* finalize the Adversary, which returna its boolean judgment *)

  proc final(tpv : tp_view) : bool {O.hash}
}.

(*************************** Real and Ideal Games *****************************)

(* the "real" game

   parameterized by Adversary, which is given limited access to random
   oracle *)

module GReal(Adv : ADV) : GAME = {
  module Or  = RO.Or        (* random oracle *)
  module LOr = LRO.LOr(Or)  (* limited random oracle built from Or *)
  module A   = Adv(LOr)     (* specialization of Adversary to LOr *)

  (* custom environment to be passed to Protocol *)

  module Env : ENV = {
    var qrys_ctr : int  (* number of queries processed *)

    proc init_and_get_db() : db option = {
      var db_opt : db option;
      qrys_ctr <- 0;
      LOr.init();  (* Or.init is called by Protocol.main *)
      db_opt <@ A.init_and_get_db(Protocol.tpv);
      return db_opt;
    }

    proc get_qry() : elem option = {
      var qry_opt : elem option;
      qry_opt <@ A.get_qry(Protocol.tpv);
      if (qry_opt <> None) {
        if (qrys_ctr < qrys_max) {
          qrys_ctr <- qrys_ctr + 1;
        }
        else {
          qry_opt <- None;  (* Adversary has proposed too many queries *)
        }
      }
      return qry_opt;
    }

    proc put_qry_count(cnt : int) : unit = {
      (* ignore the count *)
      A.qry_done(Protocol.tpv);
    }

    proc final() : bool = {
      var b : bool;
      b <@ A.final(Protocol.tpv);
      return b;
    }
  }

  proc main() : bool = {
    var b : bool;
    b <@ Protocol(Env).main();
    return b;
  }
}.

(* module type for TP's Simulator

   Simulator can't use RO.Or - because of module restriction in
   top-level theorem *)

module type SIM = {
  (* initialization *)

  proc * init() : unit

  (* get current view *)

  proc get_view() : tp_view

  (* receive hashed database *)

  proc receive_hdb(hdb : hdb) : unit
    
  (* count occurrences of tag in hashed database *)

  proc count_tag(tag : tag) : int
}.

(* the "ideal" game

   parameterized by Adversary and Simulator for TP

   doesn't make use of Server/Client shared secret, but Server and
   Client hash elements using shared private random oracle

   Adversary has limited access to random oracle *)

module GIdeal(Adv : ADV, Sim : SIM) : GAME = {
  module Or  = RO.Or        (* random oracle *)
  module LOr = LRO.LOr(Or)  (* limited random oracle built from Or *)
  module A   = Adv(LOr)     (* specialization of Adversary to LOr *)
  module POr = Priv.Or      (* private random oracle for elements *)

  var hdb : hdb       (* hashed database *)
  var qrys_ctr : int  (* number queries processed *)

  proc server_hash_db(db : db) : unit = {
    var i : int; var elem : elem; var tag : tag;
    db <@ Shuffle.shuffle(db);
    hdb <- []; i <- 0;
    while (i < size db) {
      elem <- nth elem_default db i;
      tag <@ POr.hash(elem);  (* private oracle *)
      hdb <- hdb ++ [tag];
      i <- i + 1;
    }
  }

  proc client_loop() : unit = {
    var tag : tag; var qry_opt : elem option;
    var not_done : bool <- true;
    var tpv : tp_view;
    while (not_done) {
      tpv <@ Sim.get_view(); qry_opt <@ A.get_qry(tpv);
      if (qry_opt = None) {
        not_done <- false;
      }
      elif (qrys_ctr < qrys_max) {
        qrys_ctr <- qrys_ctr + 1;
        tag <@ POr.hash(oget qry_opt);  (* private oracle *)
        Sim.count_tag(tag);  (* result is discarded *)
        tpv <@ Sim.get_view(); A.qry_done(tpv);
      }
      else {  (* Adversary has proposed too many queries *)
        not_done <- false;
      }
    }
  }

  proc main() : bool = {
    var db_opt : db option; var b : bool; var tpv : tp_view;
    Sim.init(); qrys_ctr <- 0;
    Or.init(); LOr.init(); POr.init();
    tpv <@ Sim.get_view(); db_opt <@ A.init_and_get_db(tpv);
    if (db_opt <> None) {
      server_hash_db(oget db_opt);
      Sim.receive_hdb(hdb);
      client_loop();
    }
    tpv <@ Sim.get_view(); b <@ A.final(tpv);
    return b;
  }
}.

(* see end-of-file for top-level theorem *)

(********************************* Proof Body *********************************)

(* TP's Simulator *)

module Sim : SIM = {
  var tpv : tp_view
  var hdb : hdb

  proc init() : unit = {
    tpv <- []; hdb <- [];
  }

  proc get_view() : tp_view = {
    return tpv;
  }

  proc receive_hdb(hdb' : hdb) : unit = {
    hdb <- hdb';
    tpv <- tpv ++ [tpv_got_hdb hdb'];
  }

  proc count_tag(tag : tag) : int = {
    var i, cnt : int;
    cnt <- 0; i <- 0;
    while (i < size hdb) {
      if (nth zeros_tag hdb i = tag) {
        cnt <- cnt + 1;
      }
      i <- i + 1;
    }
    tpv <- tpv ++ [tpv_tag_count(tag, cnt)];
    return cnt;
  }
}.

(************************* Theories Supporting Proof **************************)

(* secrecy random oracles *)

require SecrecyRandomOracle.  (* abstract theory *)

(******************************** Proof Section *******************************)

(* the rest of the proof is within a section, in which the Adversary,
   Adv, is declared locally *)

section.

declare module Adv <: ADV{GReal, GIdeal, Sim}.

(* these axioms will be preconditions of the lemma we export
   from section *)

declare axiom init_and_get_db_ll :
  forall (O <: RO.OR{Adv}),
  islossless O.hash => islossless Adv(O).init_and_get_db.

declare axiom get_qry_ll :
  forall (O <: RO.OR{Adv}),
  islossless O.hash => islossless Adv(O).get_qry.

declare axiom qry_done_ll :
  forall (O <: RO.OR{Adv}),
  islossless O.hash => islossless Adv(O).qry_done.

declare axiom final_ll :
  forall (O <: RO.OR{Adv}),
  islossless O.hash => islossless Adv(O).final.

(* G1 is like GReal(Adv), except that inlining and dead code
   elimination have been done, and the Server and Client do their
   hashing using a new hash_elem procedure that takes in an element
   and hashes that element paired with the shared secret *)

local module G1 : GAME = {
  module Or  = RO.Or
  module LOr = LRO.LOr(Or)
  module A   = Adv(LOr)

  var tpv      : tp_view
  var sec      : sec
  var hdb      : hdb
  var qrys_ctr : int

  proc hash_elem(elem : elem) : tag = {
    var tag : tag;
    tag <@ RO.Or.hash((elem, sec));
    return tag;
  }

  proc server_hash_db(db : db) : unit = {
    var i : int;
    var elem : elem;
    var tag : tag;
    db <- Shuffle.shuffle(db);
    hdb <- []; i <- 0;
    while (i < size db) {
      elem <- nth elem_default db i;
      tag <@ hash_elem(elem);
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
    tpv <- tpv ++ [tpv_tag_count(tag, cnt)];
    return cnt;
  }

  proc client_loop() : unit = {
    var tag : tag;
    var qry_opt : elem option;
    var not_done : bool <- true;
    while (not_done) {
      qry_opt <@ A.get_qry(tpv);
      if (qry_opt = None) {
        not_done <- false;
      }
      elif (qrys_ctr < qrys_max) {
        qrys_ctr <- qrys_ctr + 1;
        tag <@ hash_elem(oget qry_opt);
        tp_count_tag(tag);
        A.qry_done(tpv);
      }
      else {
        not_done <- false;
      }
    }
  }

  proc main() : bool = {
    var db_opt : db option;
    var b : bool;
    tpv <- [];
    Or.init(); LOr.init();
    sec <$ sec_distr; qrys_ctr <- 0;
    db_opt <@ A.init_and_get_db(tpv);
    if (db_opt <> None) {
      server_hash_db(oget db_opt);
      tpv <- tpv ++ [tpv_got_hdb hdb];
      client_loop();
    }
    b <@ A.final(tpv);
    return b;
  }
}.

local lemma Protocol_GReal_Env_G1_server_hash_db :
  equiv
  [Protocol(GReal(Adv).Env).server_hash_db ~ G1.server_hash_db :
   ={db, glob LRO.LOr(RO.Or)} /\
   Protocol.server_sec{1} = G1.sec{2} ==>
   Protocol.server_hdb{1} = G1.hdb{2} /\ ={glob LRO.LOr(RO.Or)}].
proof. proc; inline G1.hash_elem; sim. qed.

local lemma Protocol_GReal_Env_G1_client_loop :
  equiv
  [Protocol(GReal(Adv).Env).client_loop ~ G1.client_loop :
   ={glob LRO.LOr(RO.Or), glob Adv} /\ Protocol.client_sec{1} = G1.sec{2} /\
   GReal.Env.qrys_ctr{1} = G1.qrys_ctr{2} /\ Protocol.tp_hdb{1} = G1.hdb{2} /\
   Protocol.tpv{1} = G1.tpv{2} ==>
   ={glob LRO.LOr(RO.Or), glob Adv} /\
   GReal.Env.qrys_ctr{1} = G1.qrys_ctr{2} /\ Protocol.tpv{1} = G1.tpv{2}].
proof.
proc.
inline G1.hash_elem GReal(Adv).Env.get_qry GReal(Adv).Env.put_qry_count.
sp.
while
  (={not_done, glob LRO.LOr(RO.Or), glob Adv} /\
   Protocol.client_sec{1} = G1.sec{2} /\
   GReal.Env.qrys_ctr{1} = G1.qrys_ctr{2} /\ Protocol.tp_hdb{1} = G1.hdb{2} /\
   Protocol.tpv{1} = G1.tpv{2}).
seq 1 1 :
  (={not_done, glob LRO.LOr(RO.Or), glob Adv} /\
   qry_opt0{1} = qry_opt{2} /\ Protocol.client_sec{1} = G1.sec{2} /\
   GReal.Env.qrys_ctr{1} = G1.qrys_ctr{2} /\ Protocol.tp_hdb{1} = G1.hdb{2} /\
   Protocol.tpv{1} = G1.tpv{2}); first sim.
case (qry_opt{2} = None).
rcondf{1} 1; first auto.
rcondt{2} 1; first auto.
sp.
rcondt{1} 1; first auto.
auto.
rcondt{1} 1; first auto.
rcondf{2} 1; first auto.
if => //.
rcondf{1} 4; first auto.
call (_ : ={glob LRO.LOr(RO.Or)}); first sim.
wp.
call
  (_ : Protocol.tp_hdb{1} = G1.hdb{2} /\ Protocol.tpv{1} = G1.tpv{2});
  first sim.
sp; wp.
call (_ : ={RO.Or.mp}); first sim.
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
seq 11 5 :
  (={glob LRO.LOr(RO.Or)} /\ Protocol.server_sec{1} = G1.sec{2} /\
   GReal.Env.qrys_ctr{1} = G1.qrys_ctr{2} /\
   Protocol.client_sec{1} = G1.sec{2} /\ Protocol.tpv{1} = G1.tpv{2}).
swap{2} 4 -2; inline*; auto.
seq 2 1 :
  (={glob LRO.LOr(RO.Or), glob Adv} /\ Protocol.server_sec{1} = G1.sec{2} /\
   Protocol.client_sec{1} = G1.sec{2} /\
   GReal.Env.qrys_ctr{1} = G1.qrys_ctr{2} /\
   Protocol.tpv{1} = G1.tpv{2} /\ ={db_opt}); first sim.
if => //.
wp.
call (_ : ={glob LRO.LOr(RO.Or)}); first sim.
call Protocol_GReal_Env_G1_client_loop.
wp.
call Protocol_GReal_Env_G1_server_hash_db.
auto.
sim.
qed.

local lemma GReal_G1 &m :
  Pr[GReal(Adv).main() @ &m : res] = Pr[G1.main() @ &m : res].
proof. by byequiv GReal_G1_main. qed.

(* we locally clone the abstract theory SecrecyRandomOracle as the
   theory SRO, fully realizing it *)

local clone SecrecyRandomOracle as SRO with
  type elem <- elem,
  op output_len <- tag_len,
  type output <- tag,
  op output_default <- zeros_tag,
  op output_distr <- tag_distr,
  op sec_len <- sec_len,
  type sec <- sec,
  op sec_default <- zeros_sec,
  op sec_distr <- sec_distr,
  op limit <- limit
proof *.
(* beginning of realization *)
realize output_len_ge0. apply tag_len_ge0. qed.

realize mu1_output_distr. apply mu1_tag_distr. qed.

realize output_distr_ll. apply tag_distr_ll. qed.

realize sec_len_ge0. apply sec_len_ge0. qed.

realize mu1_sec_distr. apply mu1_sec_distr. qed.

realize sec_distr_ll. apply sec_distr_ll. qed.

realize limit_ge0. apply limit_ge0. qed.
(* end of realization *)

(* convert a secrecy random oracle to a random oracle (to be given to
   adversary, which lacks access to init) *)

local module SecOrToOr(SOr : SRO.SEC_OR) : RO.OR = {
  proc init() : unit = {  (* dummy -- just for typechecking *)
  }

  proc hash(inp : elem * sec) : tag = {
    var tag : tag;
    tag <@ SOr.lhash(inp);  (* limited hashing *)
    return tag;
  }
}.

(* concrete secrecy adversary, parameterized by a secrecy random
   oracle

   like G1, except that the use of the shared secret has been removed,
   oracle initialization has been removed, calls to hash_elem have been
   replaced by calls to the hash procedure of the secrecy random
   oracle, and Adv is given the random oracle derived by SecOrToOr from the
   secrecy random oracle *)

local module (SecAdv : SRO.SEC_ADV) (SOr : SRO.SEC_OR) = {
  module A = Adv(SecOrToOr(SOr))

  var tpv : tp_view
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
      tag <@ SOr.hash(elem);
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
    tpv <- tpv ++ [tpv_tag_count(tag, cnt)];
    return cnt;
  }

  proc client_loop() : unit = {
    var tag : tag;
    var qry_opt : elem option;
    var not_done : bool <- true;
    while (not_done) {
      qry_opt <@ A.get_qry(tpv);
      if (qry_opt = None) {
        not_done <- false;
      }
      elif (qrys_ctr < qrys_max) {
        qrys_ctr <- qrys_ctr + 1;
        tag <@ SOr.hash(oget qry_opt);
        tp_count_tag(tag);
        A.qry_done(tpv);
      }
      else {
        not_done <- false;
      }
    }
  }

  proc main() : bool = {
    var db_opt : db option;
    var b : bool;
    tpv <- []; qrys_ctr <- 0;
    hdb <- [];  (* redundant, but needed for rewriting with SRO.GDep_GIndep *)
    db_opt <@ A.init_and_get_db(tpv);
    if (db_opt <> None) {
      server_hash_db(oget db_opt);
      tpv <- tpv ++ [tpv_got_hdb hdb];
      client_loop();
    }
    b <@ A.final(tpv);
    return b;
  }
}.

(* we need to show that the main procedure of SecAdv is lossless *)

local lemma SecAdv_server_hash_db_ll :
  forall (SOr <: SRO.SEC_OR),
  islossless SOr.hash =>
  islossless SecAdv(SOr).server_hash_db.
proof.
move => SOr hash_ll; proc.
while (true) (size db - i).
auto.
call (_ : true).
auto; smt().
wp.
call (_ : true ==> true); first apply Shuffle_shuffle_ll.
auto; smt().
qed.

local lemma SecAdv_tp_count_tag_ll :
  forall (SOr <: SRO.SEC_OR),
  islossless SecAdv(SOr).tp_count_tag.
proof.
move => SOr; proc; wp.
while (true) (size SecAdv.hdb - i).
auto; smt().
auto; smt().
qed.

local lemma SecAdv_client_loop_ll :
  forall (SOr <: SRO.SEC_OR{SecAdv}),
  islossless SOr.lhash => islossless SOr.hash =>
  phoare
  [SecAdv(SOr).client_loop :
   SecAdv.qrys_ctr <= qrys_max ==> true] = 1%r.
proof.
move => SOr lhash_ll hash_ll; proc; sp.
while (SecAdv.qrys_ctr <= qrys_max)
      (b2i not_done * (qrys_max - SecAdv.qrys_ctr + 1)).
auto.
seq 1 :
  (SecAdv.qrys_ctr <= qrys_max /\ not_done /\
   b2i not_done * (qrys_max - SecAdv.qrys_ctr + 1) = z).
auto.
call (_ : true ==> true).
apply (get_qry_ll (SecOrToOr(SOr))); proc; call lhash_ll; auto.
auto.
if => //.
auto; smt().
if => //.
call (_ : true ==> true).
apply (qry_done_ll (SecOrToOr(SOr))); proc; call lhash_ll; auto.
call (SecAdv_tp_count_tag_ll SOr).
call hash_ll.
auto; smt().
auto; smt().
hoare.
call (_ : true); first proc; auto.
auto.
trivial.
auto; smt().
qed.

local lemma SecAdv_main_ll :
  forall (SOr <: SRO.SEC_OR{SecAdv}),
  islossless SOr.lhash => islossless SOr.hash =>
  islossless SecAdv(SOr).main.
proof.
move => SOr lhash_ll hash_ll; proc.
call (_ : true ==> true).
apply (final_ll (SecOrToOr(SOr))); proc; call lhash_ll; auto.
seq 4 : (SecAdv.qrys_ctr = 0).
auto.
sp; call (_ : true ==> true).
apply (init_and_get_db_ll (SecOrToOr(SOr)));
  proc; call lhash_ll; auto.
auto.
if => //.
call (_ : SecAdv.qrys_ctr <= qrys_max ==> true).
apply (SecAdv_client_loop_ll SOr);
  [apply lhash_ll | apply hash_ll].
wp; call (_ : true ==> true).
apply (SecAdv_server_hash_db_ll SOr); apply hash_ll.
auto.
smt(qrys_max_ge0).
hoare; auto.
sp; call (_ : true ==> true); first proc true => //.
auto.
trivial.
qed.

(* preparation for showing equivalence between G1 and SRO.GDep(SecAdv) *)

local lemma G1_SRO_SecOrDep_hash_elem_hash (xs : (elem * sec) fset) :
  equiv
  [G1.hash_elem ~ SRO.SecOrDep.hash :
   ={elem} /\
   G1.sec{1} = SRO.SecOrDep.secret{2} /\ ={mp}(RO.Or, SRO.SecOrDep) /\
   xs = fdom RO.Or.mp{1} ==>
   ={res} /\ ={mp}(RO.Or, SRO.SecOrDep) /\ xs \subset fdom RO.Or.mp{1}].
proof.
proc.
inline RO.Or.hash.
seq 1 0 :
  (={elem} /\ G1.sec{1} = SRO.SecOrDep.secret{2} /\
   ={mp}(RO.Or, SRO.SecOrDep) /\ xs = fdom RO.Or.mp{1} /\
   inp{1} = (elem{2}, SRO.SecOrDep.secret{2})); first auto.
wp; if => //; auto; progress.
rewrite subsetP => el mem_dom_mp_el.
smt(mem_fdom mem_set).
qed.

local lemma LRO_LOr_RO_Or_SecOrToOr_SRO_SecOrDep_hash :
  equiv
  [LRO.LOr(RO.Or).hash ~ SecOrToOr(SRO.SecOrDep).hash :
   ={inp} /\
   G1.sec{1} = SRO.SecOrDep.secret{2} /\
   ={mp}(RO.Or, SRO.SecOrDep) /\ ={inps, ctr}(LRO.LOr, SRO.SecOrDep) /\
   LRO.LOr.inps{1} \subset fdom RO.Or.mp{1} ==>
   ={res} /\
   ={mp}(RO.Or, SRO.SecOrDep) /\ ={inps, ctr}(LRO.LOr, SRO.SecOrDep) /\
   LRO.LOr.inps{1} \subset fdom RO.Or.mp{1}].
proof.
proc; inline SRO.SecOrDep.lhash.
seq 0 1 :
  (={inp} /\ inp0{2} = inp{2} /\ G1.sec{1} = SRO.SecOrDep.secret{2} /\
   ={mp}(RO.Or, SRO.SecOrDep) /\ ={inps, ctr}(LRO.LOr, SRO.SecOrDep) /\
   LRO.LOr.inps{1} \subset fdom RO.Or.mp{1}); first auto.
if => //.
inline RO.Or.hash; rcondf {1} 2.
auto; progress; smt(mem_fdom).
auto.
if => //.
inline RO.Or.hash; sp 3 2.
case (dom RO.Or.mp{1} inp0{1}).
rcondf {1} 1; first auto.
rcondt {2} 1; first auto.
auto; progress;
  rewrite subsetP => el; rewrite in_fsetU in_fset1; smt(mem_fdom).
rcondt {1} 1; first auto.
rcondf {2} 1; first auto.
wp; rnd; skip => /> &2
  ctr_R inps_R inps_R_sub_fdom_mp inp_not_in_inps_R _
  inp_not_in_mp mp_L _.
split.
by rewrite get_set_sameE.
rewrite subsetP => el;
 rewrite mem_fdom mem_set in_fsetU in_fset1;
  elim => [/inps_R_sub_fdom_mp /mem_fdom -> // | -> //].
auto.
qed.

local lemma G1_GDep_SecAdv_main :
  equiv
  [G1.main ~ SRO.GDep(SecAdv).main :
   true ==> ={res}].
proof.
proc.
inline LRO.LOr(RO.Or).init RO.Or.init
       SRO.GDep(SecAdv).SA.main SRO.SecOrDep.init.
seq 6 9 :
  (G1.tpv{1} = SecAdv.tpv{2} /\ G1.sec{1} = SRO.SecOrDep.secret{2} /\
   G1.qrys_ctr{1} = SecAdv.qrys_ctr{2} /\ ={mp}(RO.Or, SRO.SecOrDep) /\
   ={ctr, inps}(LRO.LOr, SRO.SecOrDep) /\
   LRO.LOr.inps{1} \subset fdom RO.Or.mp{1}).
swap{1} 5 -4; auto; progress; rewrite sub0set.
sim
  (: G1.sec{1} = SRO.SecOrDep.secret{2} /\
     ={mp}(RO.Or, SRO.SecOrDep) /\
     ={ctr, inps}(LRO.LOr, SRO.SecOrDep)) /
  (LRO.LOr.inps{1} \subset fdom RO.Or.mp{1}) :
  (={b}).
exists* RO.Or.mp{1}; elim*; move => mp_L.
conseq (G1_SRO_SecOrDep_hash_elem_hash (fdom mp_L)); smt().
conseq (LRO_LOr_RO_Or_SecOrToOr_SRO_SecOrDep_hash); smt().
qed.

local lemma G1_GDep_SecAdv &m :
  Pr[G1.main() @ &m : res] = Pr[SRO.GDep(SecAdv).main() @ &m : res].
proof. by byequiv G1_GDep_SecAdv_main. qed.

(* G2 is like GIdeal(Adv, Sim), except that inlining has been done *)

local module G2 = {
  module Or  = RO.Or
  module LOr = LRO.LOr(Or)
  module A   = Adv(LOr)
  module POr = Priv.Or

  var tpv : tp_view
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
      tag <@ POr.hash(elem);
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
    tpv <- tpv ++ [tpv_tag_count(tag, cnt)];
    return cnt;
  }

  proc client_loop() : unit = {
    var tag : tag;
    var qry_opt : elem option;
    var not_done : bool <- true;
    while (not_done) {
      qry_opt <@ A.get_qry(tpv);
      if (qry_opt = None) {
        not_done <- false;
      }
      elif (qrys_ctr < qrys_max) {
          qrys_ctr <- qrys_ctr + 1;
          tag <@ POr.hash(oget qry_opt);
          tp_count_tag(tag);
          A.qry_done(tpv);
      }
      else {
        not_done <- false;
      }
    }
  }

  proc main() : bool = {
    var db_opt : db option;
    var b : bool;
    tpv <- [];
    Or.init(); LOr.init(); POr.init();
    qrys_ctr <- 0;
    db_opt <@ A.init_and_get_db(tpv);
    if (db_opt <> None) {
      server_hash_db(oget db_opt);
      tpv <- tpv ++ [tpv_got_hdb hdb];
      client_loop();
    }
    b <@ A.final(tpv);
    return b;
  }
}.

(* preparation for showing equivalence between SRO.GIndep(SecAdv) and
   G2 *)

local lemma SecOrToOr_SRO_SecOrIndep_LRO_LOr_RO_Or_hash :
  equiv
  [SecOrToOr(SRO.SecOrIndep).hash ~ LRO.LOr(RO.Or).hash :
   ={inp} /\
   SRO.SecOrIndep.lhmp{1} = RO.Or.mp{2} /\
   ={ctr, inps}(SRO.SecOrIndep, LRO.LOr) /\
   LRO.LOr.inps{2} = fdom RO.Or.mp{2} ==>
   ={res} /\
   SRO.SecOrIndep.lhmp{1} = RO.Or.mp{2} /\
   ={ctr, inps}(SRO.SecOrIndep, LRO.LOr) /\
   LRO.LOr.inps{2} = fdom RO.Or.mp{2}].
proof.
proc; inline SRO.SecOrIndep.lhash.
seq 1 0 :
  (={inp} /\ inp0{1} = inp{1} /\
   SRO.SecOrIndep.lhmp{1} = RO.Or.mp{2} /\
   ={ctr, inps}(SRO.SecOrIndep, LRO.LOr) /\
   LRO.LOr.inps{2} = fdom RO.Or.mp{2}); first auto.
if => //.
inline RO.Or.hash.
rcondf {2} 2.
move => &m.
auto; smt(mem_fdom).
auto; smt().
if => //.
inline RO.Or.hash.
rcondt {2} 4; first auto.
auto; progress; smt(mem_fdom).
auto => /> &2 inp_not_in_mp _ outL _.
split;
  [by rewrite get_set_sameE |
   by rewrite fdom_set].
auto.
qed.

local lemma GIndep_SecAdv_G2_main :
  equiv[SRO.GIndep(SecAdv).main ~ G2.main : true ==> ={res}].
proof.
proc.
inline SRO.GIndep(SecAdv).SA.main SRO.SecOrIndep.init
       LRO.LOr(RO.Or).init RO.Or.init Priv.Or.init.
seq 8 6 :
  (SecAdv.tpv{1} = G2.tpv{2} /\ SecAdv.qrys_ctr{1} = G2.qrys_ctr{2} /\
   SRO.SecOrIndep.lhmp{1} = RO.Or.mp{2} /\
   SRO.SecOrIndep.hmp{1} = Priv.Or.mp{2} /\
   ={inps, ctr}(SRO.SecOrIndep, LRO.LOr) /\
   LRO.LOr.inps{2} = fdom RO.Or.mp{2}).
auto; progress; smt(fdom0).
sim
  (: SRO.SecOrIndep.lhmp{1} = RO.Or.mp{2} /\
     SRO.SecOrIndep.hmp{1} = Priv.Or.mp{2} /\
     ={inps, ctr}(SRO.SecOrIndep, LRO.LOr)) /
  (LRO.LOr.inps{2} = fdom RO.Or.mp{2}) :
  (={b}).
conseq (SecOrToOr_SRO_SecOrIndep_LRO_LOr_RO_Or_hash); smt().
qed.

local lemma GIndep_SecAdv_G2 &m :
  Pr[SRO.GIndep(SecAdv).main() @ &m : res] =
  Pr[G2.main() @ &m : res].
proof. by byequiv GIndep_SecAdv_G2_main. qed.

(* now we connect G1 and G2 by applying lemma SRO.GDepGIndep *)

local lemma G1_G2 &m :
  `| Pr[G1.main() @ &m : res] - Pr[G2.main() @ &m : res] | <=
  limit%r / (2 ^ sec_len)%r.
proof.
rewrite (G1_GDep_SecAdv &m) -(GIndep_SecAdv_G2 &m)
        (SRO.GDep_GIndep SecAdv &m);
apply SecAdv_main_ll.
qed.

local lemma GReal_G2 &m :
  `| Pr[GReal(Adv).main() @ &m : res] - Pr[G2.main() @ &m : res] | <=
  limit%r / (2 ^ sec_len)%r.
proof. rewrite (GReal_G1 &m); apply (G1_G2 &m). qed.

local lemma G2_GIdeal_server_hash_db :
  equiv
  [G2.server_hash_db ~ GIdeal(Adv, Sim).server_hash_db :
   ={db} /\ ={mp}(G2.POr, GIdeal.POr) ==>
   ={mp}(G2.POr, GIdeal.POr) /\ ={hdb}(G2, GIdeal)].
proof. sim. qed.

local lemma G2_GIdeal_client_loop :
  equiv
  [G2.client_loop ~ GIdeal(Adv, Sim).client_loop :
   ={qrys_ctr}(G2, GIdeal) /\ ={hdb, tpv}(G2, Sim) /\
   ={mp}(G2.Or, GIdeal.Or) /\ ={glob LRO.LOr} /\
   ={mp}(G2.POr, GIdeal.POr) /\ ={glob Adv} ==>
   ={tpv}(G2, Sim) /\ ={mp}(G2.Or, GIdeal.Or) /\
   ={glob LRO.LOr} /\ ={glob Adv}].
proof.
proc; inline Sim.get_view.
while
  (={not_done} /\ ={qrys_ctr}(G2, GIdeal) /\ ={hdb, tpv}(G2, Sim) /\
   ={mp}(G2.Or, GIdeal.Or) /\ ={glob LRO.LOr} /\
   ={mp}(G2.POr, GIdeal.POr) /\ ={glob Adv}).
seq 1 2 :
  (={not_done, qry_opt} /\ ={qrys_ctr}(G2, GIdeal) /\ ={hdb, tpv}(G2, Sim) /\
   ={mp}(G2.Or, GIdeal.Or) /\ ={glob LRO.LOr} /\
   ={mp}(G2.POr, GIdeal.POr) /\ ={glob Adv}); first sim.
if => //; first auto.
if => //; [sim | auto].
auto.
qed.

local lemma G2_GIdeal_main :
  equiv[G2.main ~ GIdeal(Adv, Sim).main : true ==> ={res}].
proof.
proc.
inline Sim.init Sim.get_view Sim.receive_hdb.
swap{2} 2 4; swap{2} 2 3.
seq 6 8 :
  (={tpv}(G2, Sim) /\ ={qrys_ctr}(G2, GIdeal) /\
   ={mp}(G2.Or, GIdeal.Or) /\ ={glob LRO.LOr} /\
   ={mp}(G2.POr, GIdeal.POr) /\ ={glob Adv, db_opt}); first sim.
call (_ : ={mp}(G2.Or, GIdeal.Or) /\ ={glob LRO.LOr}); first sim.
wp.
if => //.
call G2_GIdeal_client_loop.
wp.
call G2_GIdeal_server_hash_db.
auto.
qed.

local lemma G2_GIdeal &m :
  Pr[G2.main() @ &m : res] = Pr[GIdeal(Adv, Sim).main() @ &m : res].
proof. by byequiv G2_GIdeal_main. qed.

lemma GReal_GIdeal' &m :
  `|Pr[GReal(Adv).main() @ &m : res] -
    Pr[GIdeal(Adv, Sim).main() @ &m : res]| <=
  limit%r / (2 ^ sec_len)%r.
proof. rewrite -(G2_GIdeal &m); apply (GReal_G2 &m). qed.

end section.

(* main theorem *)

lemma GReal_GIdeal :
  exists (Sim <: SIM{GReal, GIdeal}),  (* can't use RO.Or *)
  forall (Adv <: ADV{GReal, GIdeal, Sim}) &m,
  (forall (O <: RO.OR{Adv}),
   islossless O.hash => islossless Adv(O).init_and_get_db) =>
  (forall (O <: RO.OR{Adv}),
   islossless O.hash => islossless Adv(O).get_qry) =>
  (forall (O <: RO.OR{Adv}),
   islossless O.hash => islossless Adv(O).qry_done) =>
  (forall (O <: RO.OR{Adv}),
   islossless O.hash => islossless Adv(O).final) =>
  `|Pr[GReal(Adv).main() @ &m : res] -
    Pr[GIdeal(Adv, Sim).main() @ &m : res]| <=
  limit%r / (2 ^ sec_len)%r.
proof.
exists Sim => Adv &m.
move => init_and_get_db_ll get_qry_ll qry_done_ll final_ll.
apply
  (GReal_GIdeal' Adv init_and_get_db_ll get_qry_ll qry_done_ll
   final_ll &m).
qed.
