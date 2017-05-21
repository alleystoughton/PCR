EasyCrypt Security Proof of Private Count Retrieval (PCR) Protocol
====================================================================

This repository contains the specification and proof of security for a
three party cryptographic protocol called PCR (Private Count
Retrieval) using the [EasyCrypt](https://www.easycrypt.info/trac/)
proof assistant.

PCR involves three parties: a Server, a Client and a Third Party (TP).
The protocol works with one-dimensional databases: a database consists
of a list of elements (which can be anything). Database queries are
single elements: a query is a request for the number of occurrences of
the query in the database. The database is held by the Server, and
queries are made by the Client. The Client is only allowed to learn
the counts for the queries it makes, whereas the Server must not learn
what queries the Client makes. The TP is an intermediary between the
Server and Client, but isn't trusted - it is only allowed to learn
certain element patterns. The parties are assumed to be non-colluding.

In the PCR protocol, the Server starts by sharing a secret, *sec*,
with the Client (but not the TP). It then randomly shuffles its
database, and turns the result of the shuffling into a hashed
database, which it sends to the TP. Each element, *elem*, of the
shuffled database is transformed into the hash - computed using a
random oracle - of (*elem*, *sec*). The Server's work is then
complete. For each query, *qry*, that the Client wants to make, the
Client hashes (*qry*, *sec*), and sends the resulting hash tag, *tag*,
to the TP. The TP counts the number of occurrences of *tag* in the
hashed database, and sends the resulting count back to the Client.

Honest but curious security against each of the three protocol parties
is specified using the real/ideal paradigm. The definition of the PCR
protocol maintains protocol views for the three protocol parties. The
protocol is then specialized to the "real" games for the Server, TP
and Client. Each party also has an "ideal" game in which it is obvious
the protocol party doesn't learn more than it should, but where the
party's view is still constructed by a Simulator.

Both real and ideal games are parameterized by an Adversary, which has
access to the random oracle, and adaptively chooses protocol inputs,
as a function of the protocol views that are supplied to it and its
interactions with the random oracle. At the end of a game's execution,
the Adversary is asked to make a boolean judgment, which is returned
as the game's result. The security theorems upper-bound the absolute
value of the difference between the probabilities that the real and
ideal games return true. For these upper bounds to be small, we must
limit the Adversary in different ways, depending upon the protocol
party we are proving security against. For instance, we can limit the
Adversary's use of the random oracle, or limit the number of distinct
elements in the database it proposes. Because our proofs are
information-theoretic - as opposed to relying on hardness
assumptions - in each of our security theorems, the Simulator is existentially
quantified, so that the Simulator is part of the *proof*, instead of
part of the *specification* of security.

The EasyCrypt proofs are structured using the sequence of games
approach, in which a protocol party's real and ideal games are
connected using some number of intermediate games. This horizontal
structure is supplemented with a vertical one, in which cryptographic
reductions are carried out, using previously proved lemmas that may
themselves have been proven using game sequences. To increase the
efficiency and stability of proof checking, all uses of SMT solvers
explicitly specify the EasyCrypt lemmas that the solvers may use.

The repository contains the EasyCrypt proof scripts (files with
extensions `.ec` (ordinary theories) and `.eca` (abstract theories))
proving the security of PCR.

There is also a shell script `check-all-script` for checking all
theories using two SMT provers: Alt-Ergo and Z3.

EasyCrypt Theories
--------------------------------------------------------------------

Auxiliary Theories:

 * `DistrAux.ec` - auxiliary lemmas on distributions

 * `FMapAux.ec` - auxiliary lemmas on finite maps

 * `FSetAux.ec` - auxiliary lemmas on finite sets

 * `ListAux.ec` - auxiliary lemmas on lists

Supporting Theories:

 * `Shuffle.eca` - random shuffling of lists

 * `RandomOracle.eca` - random oracles

 * `SecretGuessing.eca` - secret guessing game

 * `SecrecyRandomOracle.eca` - secrecy random oracle

 * `Inj.ec` - injective maps

 * `NumOccs.ec` - operators for counting numbers of occurrences of elements in
   lists

 * `ElemsCounts.ec` - finite maps providing counts for certain elements

PCR Protocol:

 * `Protocol.ec` - PCR Protocol and support for Server, Third Party and Client
   proofs

Proof of Security Against Server:

 * `Server.ec`

Proof of Security Against Third Party:

 * `TP.ec`

Proof of Security Against Client:

 * `Client.ec`

Authors
--------------------------------------------------------------------

These proofs were developed by [Alley Stoughton](http://alleystoughton.us)
(alley.stoughton@icloud.com), based on a collaboration with Mayank
Varia (mayank@mvaria.com).

We intend to maintain the PCR security proof as the EasyCrypt
development continues.

Acknowledgments
--------------------------------------------------------------------

The reported work was partially completed while the authors were
employed at MIT Lincoln Laboratory, funded by the Intelligence
Advanced Research Projects Activity under Air Force Contract
FA8721-05-C-0002.

It is a pleasure to acknowledge helpful discussions with Gilles
Barthe, Ran Canetti, Robert Cunningham, François Dupressoir, Benjamin
Grégoire, Jonathan Herzog, Aaron D. Jaggard, Jonathan Katz, Catherine
Meadows, Adam Petcher, Emily Shen, Pierre-Yves Strub, Arkady
Yerukhimovich and Santiago Zanella-Béguelin. Special thanks to
Zanella-Béguelin for suggesting that security against the Third Party
could be strengthened were the Server to begin by randomly shuffling
its database. Our theory for removing redundant hashing is based on a
technique invented by Grégoire, but our implementation of this
technique doesn't build on Grégoire's code and uses a slightly
different approach.
