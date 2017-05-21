(* Server.ec *)

(* Proof of Security Against Server *)

(************* PCR Protocol and Supporting Definitions and Lemmas *************)

require import Protocol.

(********************************* Adversary **********************************)

(* Adversary module type, parameterized by a random oracle *)

module type ADV(O : RO.OR) = {
  (* all procedures are supplied the current Server view; and all
     procedures can only call O.hash (not O.init) *)

  (* initialize Adversary, and try to get a database from it; None
     means refusal *)

  proc * init_and_get_db(sv : server_view) : db option {O.hash}

  (* try to get a query from Adversary; None means done supplying queries *)

  proc get_qry(sv : server_view) : elem option {O.hash}

  (* tell the Adversary that done processing its last query *)

  proc qry_done(sv : server_view) : unit {O.hash}

  (* finalize the Adversary, which returns its boolean judgment *)

  proc final(sv : server_view) : bool {O.hash}
}.

(*************************** Real and Ideal Games *****************************)

(* the "real" game

   parameterized by Adversary *)

module GReal(Adv : ADV) : GAME = {
  module Or = RO.Or    (* random oracle *)
  module A  = Adv(Or)  (* specialization of Adversary to Or *)

  (* custom environment to be passed to Protocol *)

  module Env : ENV = {
    proc init_and_get_db() : db option = {
      var db_opt : db option;
      db_opt <@ A.init_and_get_db(Protocol.sv);
      return db_opt;
    }

    proc get_qry() : elem option = {
      var qry_opt : elem option;
      qry_opt <@ A.get_qry(Protocol.sv);
      return qry_opt;
    }

    proc put_qry_count(cnt : int) : unit = {
      (* ignore the count *)
      A.qry_done(Protocol.sv);
    }

    proc final() : bool = {
      var b : bool;
      b <@ A.final(Protocol.sv);
      return b;
    }
  }

  proc main() : bool = {
    var b : bool;
    b <@ Protocol(Env).main();
    return b;
  }
}.

(* module type for Server's Simulator, parameterized by a random
   oracle

   only the main procedure may do hashing *)

module type SIM(O : RO.OR) = {
  (* initialization *)

  proc * init() : unit

  (* get current view *)

  proc get_view() : server_view

  (* rest of processing *)

  proc main(db : db) : unit {O.hash}
}.

(* the "ideal" game

   parameterized by Adversary and Simulator for Server *)

module GIdeal(Adv : ADV, Sim : SIM) : GAME = {
  module Or = RO.Or    (* random oracle *)
  module A  = Adv(Or)  (* specialization of Adversary to Or *)
  module S  = Sim(Or)  (* specialization of Simulator to Or *)

  proc client_loop() : unit = {
    var qry_opt : elem option;
    var not_done : bool <- true;
    var sv : server_view;
    while (not_done) {
      sv <@ S.get_view(); qry_opt <@ A.get_qry(sv);
      if (qry_opt = None) {
        not_done <- false;
      }
      else {
        A.qry_done(sv);  (* nothing is done with oget qry_opt *)
      }
    }
  }

  proc main() : bool = {
    var db_opt : db option; var b : bool; var sv : server_view;
    S.init(); Or.init();
    sv <@ S.get_view(); db_opt <@ A.init_and_get_db(sv);
    if (db_opt <> None) {
      S.main(oget db_opt);
      client_loop();
    }
    sv <@ S.get_view(); b <@ A.final(sv);
    return b;
  }
}.

(* see end-of-file for top-level theorem *)

(********************************* Proof Body *********************************)

(* Server's Simulator *)

module (Sim : SIM) (O : RO.OR) = {
  var sv : server_view
  var sec : sec
  var hdb : hdb

  proc init() : unit = {
    sec <$ sec_distr;
    sv <- [sv_gen_sec sec; sv_share_sec sec];
    hdb <- [];
  }

  proc get_view() : server_view = {
    return sv;
  }

  proc hash_db(db : db) : unit = {
    var i : int; var elem : elem; var tag : tag;
    sv <- sv ++ [sv_got_db db];
    db <@ Shuffle.shuffle(db);
    sv <- sv ++ [sv_shuffle db];
    hdb <- []; i <- 0;
    while (i < size db) {
      elem <- nth elem_default db i;
      tag <@ O.hash((elem, sec));
      hdb <- hdb ++ [tag];
      sv <- sv ++ [sv_elem_hash(elem, tag)];
      i <- i + 1;
    }
    sv <- sv ++ [sv_create_hdb hdb];
  }

  proc main(db : db) : unit = {
    hash_db(db);
    sv <- sv ++ [sv_share_hdb hdb];
  }
}.

(******************************** Proof Section *******************************)

(* the rest of the proof is within a section, in which the Adversary,
   Adv, is declared locally *)

section.

(* declare Adversary module -- subsequent games will reference it, instead
   of being parameterized by it *)

declare module Adv : ADV{GReal, GIdeal, Sim}.

(* G1 is the result of doing inlining and dead code elimination to
   GReal(Adv) *)

local module G1 : GAME = {
  module Or = RO.Or
  module A  = Adv(Or)

  var sv : server_view
  var sec : sec
  var hdb : hdb

  proc server_hash_db(db : db) : unit = {
    var i : int;
    var elem : elem;
    var tag : tag;
    sv <- sv ++ [sv_got_db db];
    db <- Shuffle.shuffle(db);
    sv <- sv ++ [sv_shuffle db];
    hdb <- []; i <- 0;
    while (i < size db) {
      elem <- nth elem_default db i;
      tag <@ Or.hash((elem, sec));
      hdb <- hdb ++ [tag];
      sv <- sv ++ [sv_elem_hash(elem, tag)];
      i <- i + 1;
    }
    sv <- sv ++ [sv_create_hdb hdb];
  }

  proc client_loop() : unit = {
    var qry_opt : elem option;
    var not_done : bool <- true;
    while (not_done) {
      qry_opt <@ A.get_qry(sv);
      if (qry_opt = None) {
        not_done <- false;
      }
      else {
        (* doesn't go into Server's view *)
        Or.hash((oget qry_opt, sec));
        A.qry_done(sv);
      }
    }
  }

  proc main() : bool = {
    var db_opt : db option; var b : bool;
    Or.init();
    sec <$ sec_distr;
    sv <- [sv_gen_sec sec; sv_share_sec sec];
    db_opt <@ A.init_and_get_db(sv);
    if (db_opt <> None) {
      server_hash_db(oget db_opt);
      sv <- sv ++ [sv_share_hdb hdb];
      client_loop();
    }
    b <@ A.final(sv);
    return b;
  }
}.

(* G2 is the result of doing inlining and dead code elimination to
   GIdeal(Adv, Sim) *)

local module G2 : GAME = {
  module Or = RO.Or
  module A  = Adv(Or)

  var sv : server_view
  var sec : sec
  var hdb : hdb

  proc server_hash_db(db : db) : unit = {
    var i : int;
    var elem : elem;
    var tag : tag;
    sv <- sv ++ [sv_got_db db];
    db <- Shuffle.shuffle(db);
    sv <- sv ++ [sv_shuffle db];
    hdb <- []; i <- 0;
    while (i < size db) {
      elem <- nth elem_default db i;
      tag <@ Or.hash((elem, sec));
      hdb <- hdb ++ [tag];
      sv <- sv ++ [sv_elem_hash(elem, tag)];
      i <- i + 1;
    }
    sv <- sv ++ [sv_create_hdb hdb];
  }

  proc client_loop() : unit = {
    var qry_opt : elem option;
    var not_done : bool <- true;
    while (not_done) {
      qry_opt <@ A.get_qry(sv);
      if (qry_opt = None) {
        not_done <- false;
      }
      else {
        (* hashing removed *)
        A.qry_done(sv);
      }
    }
  }

  proc main() : bool = {
    var db_opt : db option;
    var b : bool;
    Or.init();
    sec <$ sec_distr;
    sv <- [sv_gen_sec sec; sv_share_sec sec];
    db_opt <@ A.init_and_get_db(sv);
    if (db_opt <> None) {
      server_hash_db(oget db_opt);
      sv <- sv ++ [sv_share_hdb hdb];
      client_loop();
    }
    b <@ A.final(sv);
    return b;
  }
}.

local lemma Protocol_GReal_Env_G1_server_hash_db :
  equiv
  [Protocol(GReal(Adv).Env).server_hash_db ~ G1.server_hash_db :
   ={db, glob RO.Or} /\ ={sv}(Protocol, G1) /\
   Protocol.server_sec{1} = G1.sec{2} ==>
   ={sv}(Protocol, G1) /\ Protocol.server_hdb{1} = G1.hdb{2} /\
   ={glob RO.Or}].
proof. sim. qed.

local lemma Protocol_GReal_Env_G1_client_loop :
  equiv
  [Protocol(GReal(Adv).Env).client_loop ~ G1.client_loop :
   ={glob RO.Or, glob Adv} /\ ={sv}(Protocol, G1) /\
   Protocol.client_sec{1} = G1.sec{2} ==>
   ={glob RO.Or, glob Adv} /\ ={sv}(Protocol, G1)].
proof.
proc; sp.
inline GReal(Adv).Env.get_qry GReal(Adv).Env.put_qry_count.
while
  (={not_done, glob RO.Or, glob Adv} /\ ={sv}(Protocol, G1) /\
   Protocol.client_sec{1} = G1.sec{2}).
seq 3 1 : 
  (={qry_opt, not_done, glob RO.Or, glob Adv} /\
   ={sv}(Protocol, G1) /\
   Protocol.client_sec{1} = G1.sec{2}); first sim.
if => //.
auto.
call (_ : ={glob RO.Or}); first sim.
wp.
call{1} (_ : true ==> true).
proc; wp; sp.
while true (size Protocol.tp_hdb - i).
auto; smt().
auto; smt().
call (_ : ={glob RO.Or}); first sim.
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
seq 9 3 :
  (={sv}(Protocol, G1) /\ Protocol.server_sec{1} = G1.sec{2} /\
   Protocol.client_sec{1} = G1.sec{2} /\ ={glob RO.Or}).
swap{1} 5 -4; swap{2} 2 -1; swap{1} 5 -3.
wp; simplify; sim.
seq 2 1 :
  (={sv}(Protocol, G1) /\ Protocol.server_sec{1} = G1.sec{2} /\
   Protocol.client_sec{1} = G1.sec{2} /\
   ={db_opt, glob RO.Or, glob Adv}); first sim.
if => //.
wp.
call (_ : ={glob RO.Or}); first sim.
call Protocol_GReal_Env_G1_client_loop.
wp.
call Protocol_GReal_Env_G1_server_hash_db.
auto.
sim.
qed.

local lemma GReal_G1 &m :
  Pr[GReal(Adv).main() @ &m : res] = Pr[G1.main() @ &m : res].
proof. by byequiv GReal_G1_main. qed.

(* we are going to have to get rid of redundant hashing in the
   Client *)

local clone RO.RedundantHashing as RH
proof *.
(* nothing to prove *)

(* convert a hashing oracle to a random oracle, to be given to
   Adversary, which lacks access to init *)

local module HashingToOr(Hashing : RH.HASHING) : RO.OR = {
  proc init() : unit = { }

  proc hash = Hashing.hash
}.

(* concrete hashing adversary *)

local module (HashingAdv : RH.HASHING_ADV) (Hashing : RH.HASHING) = {
  module A = Adv(HashingToOr(Hashing))

  var sv : server_view
  var sec : sec
  var hdb : hdb

  proc server_hash_db(db : db) : unit = {
    var i : int;
    var elem : elem;
    var tag : tag;
    sv <- sv ++ [sv_got_db db];
    db <- Shuffle.shuffle(db);
    sv <- sv ++ [sv_shuffle db];
    hdb <- []; i <- 0;
    while (i < size db) {
      elem <- nth elem_default db i;
      tag <@ Hashing.hash((elem, sec));
      hdb <- hdb ++ [tag];
      sv <- sv ++ [sv_elem_hash(elem, tag)];
      i <- i + 1;
    }
    sv <- sv ++ [sv_create_hdb hdb];
  }

  proc client_loop() : unit = {
    var qry_opt : elem option;
    var not_done : bool <- true;
    while (not_done) {
      qry_opt <@ A.get_qry(sv);
      if (qry_opt = None) {
        not_done <- false;
      }
      else {
        Hashing.rhash((oget qry_opt, sec));
        A.qry_done(sv);
      }
    }
  }

  proc main() : bool = {
    var db_opt : db option;
    var b : bool;
    hdb <- [];
    sec <$ sec_distr;
    sv <- [sv_gen_sec sec; sv_share_sec sec];
    db_opt <@ A.init_and_get_db(sv);
    if (db_opt <> None) {
      server_hash_db(oget db_opt);
      sv <- sv ++ [sv_share_hdb hdb];
      client_loop();
    }
    b <@ A.final(sv);
    return b;
  }
}.

local lemma G1_HashingAdv_NonOptHashing_server_hash_db :
  equiv
  [G1.server_hash_db ~ HashingAdv(RH.NonOptHashing(RO.Or)).server_hash_db :
   ={db, glob RO.Or, glob Adv} /\ ={sv, sec}(G1, HashingAdv) ==>
   ={glob RO.Or, glob Adv} /\ ={sv, sec, hdb}(G1, HashingAdv)].
proof. sim. qed.

local lemma G1_HashingAdv_NonOptHashing_client_loop :
  equiv
  [G1.client_loop ~ HashingAdv(RH.NonOptHashing(RO.Or)).client_loop :
   ={glob RO.Or, glob Adv} /\ ={sv, sec}(G1, HashingAdv) ==>
   ={glob RO.Or, glob Adv} /\ ={sv, sec}(G1, HashingAdv)].
proof.
proc; sp; inline RH.NonOptHashing(RO.Or).rhash.
while (={not_done, glob RO.Or, glob Adv} /\ ={sv, sec}(G1, HashingAdv)).
seq 1 1 :
  (={qry_opt, not_done, glob RO.Or, glob Adv} /\ ={sv, sec}(G1, HashingAdv)).
sim.
if => //.
auto.
call (_ : ={glob RO.Or}); first sim.
sp.
call (_ : ={glob RO.Or}); first sim.
auto.
auto.
qed.

local lemma G1_GNonOptHashing_HashingAdv_main :
  equiv
  [G1.main ~ RH.GNonOptHashing(HashingAdv).main :
   true ==> ={res}].
proof.
proc; inline RH.GNonOptHashing(HashingAdv).HA.main.
swap{2} 3 -1; swap{2} 3 1; wp.
seq 3 4 : (={glob RO.Or} /\ ={sec, sv}(G1, HashingAdv)).
inline*; auto.
seq 1 1 :
  (={glob RO.Or, glob Adv, db_opt} /\ ={sec, sv}(G1, HashingAdv)); first sim.
if => //.
call (_ : ={glob RO.Or}); first sim.
call G1_HashingAdv_NonOptHashing_client_loop.
wp.
call G1_HashingAdv_NonOptHashing_server_hash_db.
auto.
sim.
qed.

local lemma G1_GNonOptHashing_HashingAdv &m :
  Pr[G1.main() @ &m : res] =
  Pr[RH.GNonOptHashing(HashingAdv).main() @ &m : res].
proof. by byequiv G1_GNonOptHashing_HashingAdv_main. qed.

local lemma HashingAdv_OptHashing_G2_server_hash_db :
  equiv
  [HashingAdv(RH.OptHashing(RO.Or)).server_hash_db ~ G2.server_hash_db:
   ={db, glob RO.Or, glob Adv} /\ ={sv, sec}(HashingAdv, G2) ==>
   ={glob RO.Or, glob Adv} /\ ={sv, sec, hdb}(HashingAdv, G2)].
proof. sim. qed.

local lemma HashingAdv_OptHashing_G2_client_loop :
  equiv
  [HashingAdv(RH.OptHashing(RO.Or)).client_loop ~ G2.client_loop :
   ={glob RO.Or, glob Adv} /\ ={sv, sec}(HashingAdv, G2) ==>
   ={glob RO.Or, glob Adv} /\ ={sv, sec}(HashingAdv, G2)].
proof.
proc; sp; inline RH.OptHashing(RO.Or).rhash.
while (={not_done, glob RO.Or, glob Adv} /\ ={sv, sec}(HashingAdv, G2)).
seq 1 1 :
  (={qry_opt, not_done, glob RO.Or, glob Adv} /\ ={sv, sec}(HashingAdv, G2)).
sim.
if => //.
auto.
sp.
call (_ : ={glob RO.Or}); first sim.
auto.
auto.
qed.

local lemma GOptHashing_HashingAdv_G2_main :
  equiv
  [RH.GOptHashing(HashingAdv).main ~ G2.main :
   true ==> ={res}].
proof.
proc; inline RH.GOptHashing(HashingAdv).HA.main.
swap{1} 3 -1; swap{1} 3 1; wp.
seq 4 3 : (={glob RO.Or} /\ ={sec, sv}(HashingAdv, G2)).
inline*; auto.
seq 1 1 :
  (={glob RO.Or, glob Adv, db_opt} /\ ={sec, sv}(HashingAdv, G2)); first sim.
if => //.
call (_ : ={glob RO.Or}); first sim.
call HashingAdv_OptHashing_G2_client_loop.
wp.
call HashingAdv_OptHashing_G2_server_hash_db.
auto.
sim.
qed.

local lemma GOptHashing_HashingAdv_G2 &m :
  Pr[RH.GOptHashing(HashingAdv).main() @ &m : res] =
  Pr[G2.main() @ &m : res].
proof. by byequiv GOptHashing_HashingAdv_G2_main. qed.

local lemma G1_G2 &m :
  Pr[G1.main() @ &m : res] = Pr[G2.main() @ &m : res].
proof.
by rewrite (G1_GNonOptHashing_HashingAdv &m)
           (RH.GNonOptHashing_GOptHashing HashingAdv &m)
           (GOptHashing_HashingAdv_G2 &m).
qed.

local lemma G2_server_hash_db_Sim_hash_db :
  equiv
  [G2.server_hash_db ~ Sim(RO.Or).hash_db :
   ={db, glob RO.Or} /\ ={sv}(G2, Sim) /\
   G2.sec{1} = Sim.sec{2} ==>
   ={sv}(G2, Sim) /\ G2.hdb{1} = Sim.hdb{2} /\
   ={glob RO.Or}].
proof. sim. qed.

local lemma G2_Sim_client_loop :
  equiv
  [G2.client_loop ~ GIdeal(Adv, Sim).client_loop :
   ={glob RO.Or, glob Adv} /\ ={sv}(G2, Sim) ==>
   ={sv}(G2, Sim) /\ ={glob RO.Or, glob Adv}].
proof.
proc; inline GIdeal(Adv, Sim).S.get_view; sim.
qed.

local lemma G2_GIdeal_main :
  equiv[G2.main ~ GIdeal(Adv, Sim).main : true ==> ={res}].
proof.
proc.
inline GIdeal(Adv, Sim).S.init GIdeal(Adv, Sim).S.get_view
       GIdeal(Adv, Sim).S.main.
seq 3 5 :
  (={glob RO.Or} /\ ={sv}(G2, Sim) /\ Sim.sv{2} = sv{2} /\
   G2.sec{1} = Sim.sec{2}).
swap{2} 4 -3; inline*; auto.
seq 1 1 :
  (={db_opt, glob RO.Or, glob Adv} /\ ={sv}(G2, Sim) /\
   Sim.sv{2} = sv{2} /\ G2.sec{1} = Sim.sec{2}).
call (_ : ={glob RO.Or} /\ ={sv}(G2, Sim)).
sim. auto.
if => //.
call (_ : ={glob RO.Or}); first sim.
wp.
call G2_Sim_client_loop.
wp.
call G2_server_hash_db_Sim_hash_db.
auto.
sim.
qed.
   
local lemma G2_GIdeal &m :
  Pr[G2.main() @ &m : res] = Pr[GIdeal(Adv, Sim).main() @ &m : res].
proof. by byequiv G2_GIdeal_main. qed.

lemma GReal_GIdeal' &m :
  Pr[GReal(Adv).main() @ &m : res] = Pr[GIdeal(Adv, Sim).main() @ &m : res].
proof.
by rewrite (GReal_G1 &m) (G1_G2 &m) (G2_GIdeal &m).
qed.

end section.

(* main theorem *)

lemma GReal_GIdeal :
  exists (Sim <: SIM{GReal, GIdeal}),
  forall (Adv <: ADV{GReal, GIdeal, Sim}) &m,
  Pr[GReal(Adv).main() @ &m : res] = Pr[GIdeal(Adv, Sim).main() @ &m : res].
proof.
exists Sim => Adv &m.
apply (GReal_GIdeal' Adv &m).
qed.
