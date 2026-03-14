(** * Test file 1 for mktoc with a garbage TOC to remove

    *** Table of content
    
    - 1. This
      - 1.1 That
      - 1.2 One
    - 2. A
      - 2.1 B
      - 2.2 C

    *** Some other part of this tutorial's header
*)

(** In this tutorial, we are going to search for lemmas, mostly about natural
    numbers.

    We already have all lemmas and definitions from the prelude ([Coq.Init]),
    and we require the library file [Coq.Arith.PeanoNat] which adds hundreds
    of new constants.
*)

From Coq Require Import PeanoNat.

(** ** 42. Basic [Search] queries *)

(** In its most basic form, one searches for lemmas or definitions containing
   - a given constant, eg [Nat.add], or [nat]
   - a given string to be part of the identifier
   - a given notation
*)

(** Search all lemmas where the type [nat] and the operators (_ * _) and
   (_ + _) occur. *)
Search nat (_ + _) (_ * _). (* still too much *)

(** ** 3.3.5 More sophisticated patterns *)

(** Some text *)

(** ** Filter results by logical kind and or syntax in queries *)

(** We can also [Search] for a constant defined with a specific keyword.
    For instance, the following lists all [Lemma]s whose names contain "add"
    and types contain [0]: *)
Search "add" 0 is:Lemma.

(** ** 10.1 Disambiguating strings in Search queries *)

(** ***  Some subsection *)

(** **** 2 Some subsubsection *)

(** We have seen two different usages of strings in search queries, namely,
    searching for constants whose name contains the string, such as: *)
Search "comm".

(** **** 42 Another one *)

(** or, search for constants whose type contain a notation, such as: *)
Search "||".
Search "+".

(** *** A Great subsection *)

(** **** A subsubsection ! *)

(** We have seen two different usages of strings in search queries, namely,
    searching for constants whose name contains the string, such as: *)
Search "comm".

(** **** Another subsubsection *)

(** With some text inside *)

(** **** Yet another subsubsection *)

(** So, what really happens here?
   Blah, blah, ... *)

(** ** Searching for constants with given hypotheses (parameters) or conclusions (return type) *)

(** Finally the [head] keyword is just a shorthand for [headconcl] or [headhyp]: *)
Search head:"<->".

(** ** 0.0.0 Searching inside or outside a specific module *)

(** We hope mktoc works. *)
