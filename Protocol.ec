(* Protocol.ec *)

(* PCR Protocol and Support for Server, Third Party and Client
   Proofs *)

(* This theory defines the PCR protocol, and gives defintions and
   lemmas supporting it and the Server, Third Party and Client
   Proofs. *)

prover [""].  (* no SMT solvers *)

(***************************** Standard Theories ******************************)

require export AllCore List Distr Mu_mem Dexcepted FSet FMap List
               FelTactic.
require export StdBigop. export Bigreal BRA.
require export StdOrder.
require export StdRing. export RField.
require Word.

(***************************** Auxiliary Theories *****************************)

require export DistrAux ListAux MapAux FSetAux.

(******************** Number of Unique Elements in a List *********************)

op num_uniqs (xs : 'a list) : int = card(oflist xs).

(*********************** Elements, Secrets and Hash Tags **********************)

(* abstract type of elements *)

type elem.

op elem_default : elem.  (* default element value *)

(* secret generated by the Server and shared with the Client, but not with
   Third Party (TP)

   a secret is a bitstring of length sec_len *)

op sec_len : int.  (* length of a secret *)

axiom sec_len_ge0 : 0 <= sec_len.

clone Word as Sec with
  type Alphabet.t <- bool,            (* word alphabet *)
  op Alphabet.enum <- [true; false],  (* enumeration of word alphabet *)
  op Alphabet.card <- 2,              (* size of word alphabet *)
  op n <- sec_len,                    (* word length *)
  op dchar <- false                   (* default alphabet element *)
proof
  Alphabet.enum_spec by case,
  ge0_n by apply sec_len_ge0
  (* the remaining axioms are unprovable specifications *)
rename [op] "mkword" as "bits2w"   (* bool list -> Word.word *)
       [op] "ofword" as "w2bits".  (* Word.word -> bool list *)

type sec = Sec.word.  (* type of secrets *)

op zeros_sec : sec = Sec.bits2w [].  (* the all zero secret *)

(* uniform, full and lossless distribution on secrets *)

op sec_distr : sec distr = Sec.DWord.dunifin.

lemma mu1_sec_distr (sec : sec) :
  mu1 sec_distr sec = 1%r / (2 ^ sec_len)%r.
proof.
by rewrite -Sec.word_card Sec.DWord.dunifin1E.
qed.

lemma sec_distr_ll : is_lossless sec_distr.
proof. apply Sec.DWord.dunifin_ll. qed.

(* hash tags are bitstrings of length tag_len *)

op tag_len : int.

axiom tag_len_ge0 : 0 <= tag_len.

clone Word as Tag with
  type Alphabet.t <- bool,
  op Alphabet.enum <- [true; false],
  op Alphabet.card <- 2,
  op n <- tag_len,
  op dchar <- false
proof
  Alphabet.enum_spec by case,
  ge0_n by apply tag_len_ge0
  (* the remaining axioms are unprovable specifications *)
rename [op] "mkword" as "bits2w"
       [op] "ofword" as "w2bits".

type tag = Tag.word.  (* type of tags *)

op zeros_tag : tag = Tag.bits2w [].  (* the all zero tag *)

(* uniform, full and lossless distribution on tags *)

op tag_distr : tag distr = Tag.DWord.dunifin.

lemma mu1_tag_distr (tag : tag) :
  mu1 tag_distr tag = 1%r / (2 ^ tag_len)%r.
proof.
by rewrite -Tag.word_card Tag.DWord.dunifin1E.
qed.

lemma tag_distr_ll : is_lossless tag_distr.
proof. apply Tag.DWord.dunifin_ll. qed.

(*************************** Elements Counts Maps *****************************)

require export ElemsCounts.

(* abbreviations of specialization to type elem *)

type elems_counts = elem counts.
op empty_ec = empty_counts<:elem>.

(************************** Random Shuffling of Lists *************************)

require Shuffle.  (* abstract theory *)

clone Shuffle as Shuffle' with
  type t <- elem,
  op dflt <- elem_default
proof *.
(* nothing to realize *)

export Shuffle'.

(******************************* Random Oracle ********************************)

require RandomOracle.  (* abstract theory *)

(* we clone RandomOracle as the theory RO, setting input to elem *
   sec, output to tag, and fully realizing it *)

clone RandomOracle as RO with
  type input <- elem * sec,
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

(*********************** Databases and Hashed Databases ***********************)

type db = elem list.  (* type of databases *)

type hdb = tag list.  (* type of hashed databases *)

(******************************* Parties' Views *******************************)

(* Server's view *)

type server_view_elem = [
    sv_gen_sec    of sec           (* generated secret *)
  | sv_share_sec  of sec           (* shared secret *)
  | sv_got_db     of db            (* received database *)
  | sv_shuffle    of db            (* shuffled database *)
  | sv_elem_hash  of (elem * tag)  (* hashed element, resulting in tag *)
  | sv_create_hdb of hdb           (* created hashed database *)
  | sv_share_hdb  of hdb           (* shared hashed database *)
].

type server_view = server_view_elem list.

(* TP's view *)

type tp_view_elem = [
    tpv_got_hdb   of hdb          (* received hashed database *)
  | tpv_tag_count of (tag * int)  (* count of tag queried by Client *)
].

type tp_view = tp_view_elem list.

(* Client's view *)

type client_view_elem = [
    cv_got_sec     of sec                 (* received secret *)
  | cv_got_qry     of elem option         (* received optional query *)
  | cv_query_count of (elem * tag * int)  (* query and its tag and count *)
].

type client_view = client_view_elem list.

(**************************** Protocol Environment ***************************)

(* the protocol interacts with the outside world via an environment *)

module type ENV = {
  (* initialize environment, and try to get a database from it; None
     means refusal *)

  proc init_and_get_db() : db option

  (* try get a query from the environment; None means done supplying queries *)

  proc get_qry() : elem option

  (* give environment count corresponding to last query *)

  proc put_qry_count(cnt : int) : unit

  (* finalize the environment, returning its boolean judgment *)

  proc final() : bool
}.

(********************************** Protocol *********************************)

(* module type of protocols *)

module type PROTOCOL = {
  proc main() : bool  (* run protocol *)
}.

(* protocol *)

module Protocol (Env : ENV) : PROTOCOL = {
  module Or = RO.Or  (* random oracle *)

  (* Views *)

  var sv : server_view  (* Server's view *)
  var tpv : tp_view     (* TP's view *)
  var cv : client_view  (* Client's view *)

  proc init_views() : unit = {
    sv <- []; tpv <- []; cv <- [];
  }

  (* Server *)

  var server_sec : sec  (* Server's secret *)
  var server_hdb : hdb  (* Server's hashed database *)

  proc server_gen_sec() : unit = {  (* called by main *)
    server_sec <$ sec_distr;
    sv <- sv ++ [sv_gen_sec server_sec];
  }

  proc server_get_sec() : sec = {  (* called by client_receive_sec *)
    sv <- sv ++ [sv_share_sec server_sec];
    return server_sec;
  }

  proc server_hash_db(db : db) : unit = {  (* called by main *)
    var i : int; var elem : elem; var tag : tag;
    sv <- sv ++ [sv_got_db db];
    db <@ Shuffle.shuffle(db);
    sv <- sv ++ [sv_shuffle db];
    server_hdb <- []; i <- 0;
    while (i < size db) {
      elem <- nth elem_default db i;
      tag <@ Or.hash((elem, server_sec));
      server_hdb <- server_hdb ++ [tag];
      sv <- sv ++ [sv_elem_hash(elem, tag)];
      i <- i + 1;
    }
    sv <- sv ++ [sv_create_hdb server_hdb];
  }

  proc server_get_hdb() : hdb = {  (* called by tp_receive_hdb *)
    sv <- sv ++ [sv_share_hdb server_hdb];
    return server_hdb;
  }

  (* TP *)

  var tp_hdb : hdb  (* TP's copy of hashed database *)

  proc tp_receive_hdb() : unit = {  (* called by main *)
    tp_hdb <@ server_get_hdb();
    tpv <- tpv ++ [tpv_got_hdb tp_hdb];
  }

  proc tp_count_tag(tag : tag) : int = {  (* called by client_loop *)
    var i, cnt : int;
    cnt <- 0; i <- 0;
    while (i < size tp_hdb) {
      if (nth zeros_tag tp_hdb i = tag) {
        cnt <- cnt + 1;
      }
      i <- i + 1;
    }
    tpv <- tpv ++ [tpv_tag_count(tag, cnt)];
    return cnt;
  }

  (* Client *)

  var client_sec : sec  (* Client's copy of secret *)

  proc client_receive_sec() : unit = {  (* called by main *)
    client_sec <@ server_get_sec();
    cv <- cv ++ [cv_got_sec client_sec];
  }

  proc client_loop() : unit = {
    var cnt : int; var tag : tag; var qry_opt : elem option;
    var not_done : bool <- true;
    while (not_done) {
      qry_opt <@ Env.get_qry();
      cv <- cv ++ [cv_got_qry qry_opt];
      if (qry_opt = None) {
        not_done <- false;
      }
      else {
        tag <@ Or.hash((oget qry_opt, client_sec));
        cnt <@ tp_count_tag(tag);
        cv <- cv ++ [cv_query_count(oget qry_opt, tag, cnt)];
        Env.put_qry_count(cnt);
      }
    }
  }

  (* Main *)

  proc main() : bool = {
    var db_opt : db option; var b : bool;
    init_views(); Or.init();
    server_gen_sec(); client_receive_sec();
    db_opt <@ Env.init_and_get_db();
    if (db_opt <> None) {
      server_hash_db(oget db_opt);
      tp_receive_hdb();
      client_loop();
    }
    b <@ Env.final();
    return b;
  }
}.

(*********************************** Games ************************************)

(* a game is a module that provides a main procedure taking in no arguments
   and returning a boolean *)

module type GAME = {
  proc main() : bool
}.
