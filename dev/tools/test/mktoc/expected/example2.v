(** * Test file 1 for mktoc with a garbage TOC to remove

    *** Table of content

    - 1. Basic [Search] queries
    - 2. More sophisticated patterns
    - 3. Filter results by logical kind and or syntax in queries
    - 4. Disambiguating strings in Search queries
      - 4.1 Some subsection
        - 4.1.1 Some subsubsection
        - 4.1.2 Another one
      - 4.2 A Great subsection
        - 4.2.1 A subsubsection !
        - 4.2.2 Another subsubsection
        - 4.2.3 Yet another subsubsection
    - 5. Searching for constants with given hypotheses (parameters) or conclusions (return type)
    - 6. Searching inside or outside a specific module

    *** Some other part of this tutorial's header
*)

(** In this tutorial, we are going to search for lemmas, mostly about natural
    numbers.

    We already have all lemmas and definitions from the prelude ([Coq.Init]),
    and we require the library file [Coq.Arith.PeanoNat] which adds hundreds
    of new constants.
*)

From Coq Require Import PeanoNat.

(** ** 1. Basic [Search] queries *)

(** In its most basic form, one searches for lemmas or definitions containing
   - a given constant, eg [Nat.add], or [nat]
   - a given string to be part of the identifier
   - a given notation
*)

(** Search all lemmas where the type [nat] and the operators (_ * _) and
   (_ + _) occur. *)
Search nat (_ + _) (_ * _). (* still too much *)

(** ** 2. More sophisticated patterns *)

(** Some text *)

(** ** 3. Filter results by logical kind and or syntax in queries *)

(** We can also [Search] for a constant defined with a specific keyword.
    For instance, the following lists all [Lemma]s whose names contain "add"
    and types contain [0]: *)
Search "add" 0 is:Lemma.

(** ** 4. Disambiguating strings in Search queries *)

(** *** 4.1 Some subsection *)

(** **** 4.1.1 Some subsubsection *)

(** We have seen two different usages of strings in search queries, namely,
    searching for constants whose name contains the string, such as: *)
Search "comm".

(** **** 4.1.2 Another one *)

(** or, search for constants whose type contain a notation, such as: *)
Search "||".
Search "+".

(** *** 4.2 A Great subsection *)

(** **** 4.2.1 A subsubsection ! *)

(** We have seen two different usages of strings in search queries, namely,
    searching for constants whose name contains the string, such as: *)
Search "comm".

(** **** 4.2.2 Another subsubsection *)

(** With some text inside *)

(** **** 4.2.3 Yet another subsubsection *)

(** So, what really happens here?
   Blah, blah, ... *)

(** ** 5. Searching for constants with given hypotheses (parameters) or conclusions (return type) *)

(** Finally the [head] keyword is just a shorthand for [headconcl] or [headhyp]: *)
Search head:"<->".

(** ** 6. Searching inside or outside a specific module *)

(** We hope mktoc works. *)
