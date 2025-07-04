(** * Basic library files and modules management

    *** Summary

    This tutorial is about how to get the most out of library files, that is
    Coq files containing definitions, lemmas, notations, ...

    Coq Library files are modules, which may themselves contain (non-file) inner
    modules. In order to reuse the content of a file, one has to [Require] it
    first. We will first see how these library files are identified by Coq and
    how to [Require] them in practice.

    Coq Modules provide, among other things, namespace facilities as well as
    some form of locality. We will see how to identify the constants
    (definitions, lemmas, ...) contained in a module with a (more or less)
    qualified name such as [Bool.andb_true_l]. In order to use an unqualified
    name, such as [andb_true_l], one has to [Import] this module. It turns out
    this can lead to shadowing other existing constants. We will detail when and
    how it may happen.

    Next, we will be interested with other content types in modules, that is,
    hints, coercions, notations, ... and how they are typically not available
    when the module is not [Import]ed. We will see how to restrict what is
    visible outside a module, either from the user side with selective imports,
    or from the module writer side with locality attributes.

    We will finally clarify the difference between [Import]ing and [Export]ing a
    module.

    The second and third part of this tutorial are (almost) independent.

    These topics are often skipped from lectures or courses about Coq
    because they are mostly technical and somewhat boring. However, any Coq
    user needs to learn (usually the hard way) this content before writing their
    own libraries.

    *** Table of content

    - 1. Library files, modules and identifiers
      - 1.1 The [Require] command and fully qualified names
      - 1.2. Basic modules and the [Import] command
      - 1.3. Name clashes and disambiguation
      - 1.4. Other content types in modules
      - 1.5. Guidelines about the order of [Require] and [Import] commands
    - 2. Fine control over module features
      - 2.1. On the user's side: selective import
      - 2.2. On the writer's side: locality attributes in modules
    - 3. The [Export] command

    *** Prerequisites

    Needed:
    - The user should already have some basic Coq experience: writing
      definitions, lemmas, proofs...
    - Some parts deal with more advanced Coq content (user-defined tactics,
      notations, coercions...); having some basic knowledge about it is better
      to appreciate what Coq can offer, but is not really needed.

    Installation:
    This tutorial should work for Coq V8.17 or later.
*)

(** ** 1. Library files, modules and identifiers *)

(** *** 1.1 The [Require] command and fully qualified names *)

(** Coq's basic compilation unit is the _library file_. Each compiled file can
    be [Require]d in order to make its logical and computational content
    available in the current file.

    If not stated otherwise (with the [-noinit] command-line flag), Coq's
    initial state is populated by a dozen library files called the [Prelude]
    (the interested reader can consult its
    #<a href="https://github.com/coq/coq/blob/master/theories/Init/Prelude.v">source code</a>#).

    We can see these files with the [Print Libraries] command: *)
Print Libraries.

(** As we can see, these files share a common logical prefix made of:
    - [Coq]: the library prefix used by the standard library
    - [Init]: the subdirectory of the root directory of Coq's standard library
      where these library files are located

    This means that the [Init] directory contains the (compiled) files
    [Notations.vo], [Ltac.vo], [Logic.vo], ... and we can already use their
    content, for instance the commutativity of the disjunction: *)
Check or_comm.

(** Let's require another small library file. *)
From Coq Require Bool.Bool.

(** The previous command told [Coq] to load all logical and computational
    content in the file [Bool.vo] contained in the directory [Bool] of the root
    directory of Coq's standard library (the interested reader can browse its
    current
    #<a href="https://github.com/coq/coq/blob/master/theories/Bool/Bool.v">source code</a>#).
*)

(** Now let's see how our list of libraries has evolved: *)
Print Libraries.

(** As we can see, we have not one but two more library files.
    The [Coq.Classes.DecidableClass] is itself required in [Coq.Bool.Bool].

    Now there are two very important message here:
    1. When we [Require] a file, we [Require] recursively any file it has
       [Require]d (and any file [Require]d in the [Require]d files, and so on).
    2. There is **no way** to "unrequire" anything. Once a file has been
       required, its content will remain in the global environment of the user
       in every file where it was (transitively) required, possibly cluttering
       up [Search] output.

    As a consequence, one should be careful of what one [Require]s. *)

(** Now that we have required [Coq.Bool.Bool], we have many more lemmas about
    boolean operations. *)
Search andb true.

(** Some of them are _qualified_ with the [Bool.] prefix, these come from
    [Coq.Bool.Bool]. Others have short names, these come from one of the
    [Coq.Init] files.

    Using the [About] command gives us their locations. *)
About andb_prop.

(** Now let's take a look at [Bool.andb_true_l] *)
About Bool.andb_true_l.

(** We see that it expands to [Coq.Bool.Bool.andb_true_l]. This is the internal
    name Coq uses to distinguish it from any other constant.
    We call it an _absolutely qualified identifier_ or _fully qualified
    identifier_.

    This is a technical but important notion, so we should take some time to
    describe this identifier. There are several parts separated by dots.
    - The first part is Coq: it is the _logical name_ of the library. Other
      mechanisms (for instance a [_CoqProject] file, or [-R] and [-Q] options
      for [coqc], locations which are known by [coqc], such as the output of
      [coqc -where], ...) associate a logical name to a physical directory
      in the user's system which is the root directory of this library.
    - The second and third part correspond to the path of the file (relative to
      the root of the library) containing the identifier in the given library,
      in our case, on a Unix family system, it corresponds to [Bool/Bool.vo].

    Now, at this point, [Coq.Bool.Bool] is the last required library file
    called [Bool] containing a constant named [andb_true_l], so Coq accepts
    (and prints) as a shorter _partially qualified_ the identifier
    [Bool.andb_true_l].

    Another valid partially qualified identifier for the same constant is
    [Bool.Bool.andb_true_l].

    All these identifiers refer to the same constant: *)
About Coq.Bool.Bool.andb_true_l.
About Bool.Bool.andb_true_l.
About Bool.andb_true_l.

(** However, at this point Coq does not accept the unqualified [andb_true_l] as
    a valid identifier: *)
Fail Check andb_true_l.

(** Coq does not allow us to use this _short name_ automatically because it
    risks to silently shadow another constant with the same short name. *)

(** The [Locate] command shows all constants associated to an unqualified
    identifier and how to refer to it in the shortest way possible. *)
Locate andb_true_l.

(** If we want to use such a _short name_, we need to [Import] the [Bool]
    module (yes, we said module here and not library file, more about this
    later). *)
Import Bool.

(** Now we can refer to the constants in [Bool] with their short names. *)
Check andb_true_l.

(** Coq will also display short names in its messages: *)
Search andb true.
Search andb true inside Bool.

(** In passing, we have [Import]ed [Bool] with a small unqualified name because
    there was no confusion: *)
Locate Bool.

(** But we can refer to the [Bool] with a more qualified name too: *)
About Bool.Bool.
About Coq.Bool.Bool.

(** In fact, most users prefer short names to fully qualified names so, in
    practice, one usually [Require]s and [Import]s a file at the same time.
    This is done, for instance, with the syntax:
    [From Coq Require Import Bool.Bool.]

    In passing, there are many more possibilities to [Require] (with or with
    [Import]) a library file.
    The fully qualified name of this file is [Coq.Bool.Bool], and one can
    factor any prefix in the [From] part of the command, so the following
    command achieves the same goal:
    [From Coq.Bool Require Import Bool.]
    or, with an empty [From] part:
    [Require Import Coq.Bool.Bool.]

    In fact, the [From] part is mostly a convenience to require multiple parts
    from a common library or sublibrary. For instance, if one uses the mathcomp
    library, the single line:
    [From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.]
    loads and imports 6 files from the mathcomp library.

    If there is no confusion, it is even possible to omit the directory (or
    directories) part. In our case there is only one file [Bool.vo] in all
    Coq's standard library, so we could also have used
    [From Coq Require Import Bool.]

    What to choose is then mostly a matter of taste (and clearly depends on the
    number of files in the library). *)

(** *** 1.2. Basic modules and the [Import] command *)

(** We will use modules here mostly because they will help us understand how
    to get what we want from library files (and reject, if possible, what we
    don't want). *)

(** For now let us consider a very simple module: *)
Module Foo.
  Definition foo := 42.
  Lemma bar : 21 * 2 = foo.
  Proof. reflexivity. Qed.
  Lemma baz : 21 + 21 = foo.
  Proof. reflexivity. Qed.
End Foo.

(** Such a module, written down explicitly with [End module_name] at the end
    is called an _interactive module_.
    Our module [Foo] has 1 definition and 2 lemmas. It's printed out in the
    following way: *)
Print Module Foo.

(** Notice that, surprisingly, the too lemmas are printed as [Parameter]s, but
    they really are actual lemmas.

    We can access the content of the module with the dot syntax. *)
Print Foo.foo.
Check Foo.bar.
Check Foo.baz.

(** [Foo.bar] and [Foo.baz] are not [Parameters] or [Axioms]: the following
    [Print Assumptions] commands show that they are "closed under the global
    context", that is they do not rely on any axiom and are indeed proved. *)
Print Assumptions Foo.bar.
Print Assumptions Foo.baz.

(** But we cannot yet access them with short names: *)
Fail Check bar.
Locate bar.

(** The content of the module [Foo] can be used just like any other definitions
    and lemmas *)
Lemma forty : Foo.foo - 2 = 40.
Proof.
  unfold Foo.foo.
  fold Foo.foo.
  rewrite <-Foo.bar.
  reflexivity.
Qed.

(** This dot syntax is reminiscent of what we used for library files, and it is
    no accident. In fact,

    _library files are modules_.

    This is the most important fact to take home from this tutorial, and the
    main reason to study a part of Coq's module system.

    We can even print the content of library files, viewed as modules: *)
Print Module Coq.Bool.Bool.

(** [Import] is actually a module command, so we can: *)
Import Foo.

(** Now that [Foo] is [Import]ed, we can access its content with short names: *)
Check bar.

(** To sum up without subtlety what we have learned so far:
    - We _[Require] library files_ to load their content.
    - We _[Import] modules_ to use short names for their content (among other
      things we will see shortly)
    - _Library files are modules_. *)

(** *** 1.3. Name clashes and disambiguation *)

(** When we [Import]ed our [Foo] module before, there was no possible name
    clash since no constant in our context were named [foo], [bar] or [baz].

    In real life Coq, however, global contexts can be huge and there will
    be name clashes.

    So, what happens if we define and import the following module? *)
Module OtherFoo.
  Definition foo := true.
End OtherFoo.

Import OtherFoo.
(** First, Coq emits no error or warning, so this is a legit operation.
    What is [foo] now? *)
Print foo.
About foo.

(** Our [OtherFoo.foo] identifier has actually _shadowed_ [Foo.foo].

    To identify it, we now need to use a more qualified name. *)
Print Foo.foo.
About Foo.foo.

(** The [Locate] command shows the list of identifiers whose unqualified name
    is the given argument: *)
Locate foo.

(** The first item in the list is our [OtherFoo.foo] constant, it is available
    by its short name. Next is [Foo.foo] and Coq gives us the shortest partially
    qualified name to refer to it.

    What happens if we now [Import Foo] again? *)
Import Foo.
Print foo.
About foo.
Locate foo.

(** We have changed again to which constant refers the short name [foo]!
    Our [Foo.foo] constant is now the first item in our list of [foo] constants.
    This changing short name resolution may look innocuous but it has a very
    important consequence:

    _The order of the [Import] commands matters, changing it can break things_.
*)

(** Notice that one can always use more qualified names, so that the resulting
    code is independent of the [Import] orders: *)
Print Foo.foo.
Print OtherFoo.foo.

(** Now, for a real life example, let us consider the library files
    [Coq.Arith.PeanoNat] and [Coq.ZArith.BinInt] which contain the bulk
    of Coq's standard library content for, respectively Peano natural numbers
    and (binary) integers. *)

From Coq Require Import Arith.PeanoNat ZArith.BinInt.

(** Most of the results and operations are actually contained in the interactive
    (inner) modules [PeanoNat.Nat] and [BinInt.Z]. These inner modules are not
    imported, yet. *)
Check Nat.add_0_r.
Check Z.add_0_r.

(** Notice that the name [add_0_r] is used both for natural numbers and for
    integers, which seems right.

    At this point, [add_0_r] does not refer to anything. *)
Fail Check add_0_r.
Locate add_0_r.

(** We may choose to [Import Nat] if, for instance, our current development
    deals more with natural numbers than integers. *)
Import Nat.
Check add_0_r.
About add_0_r.

(** We could even [Import] both modules, but then beware that the order is
    important. *)
Import Z.
Check add_0_r.
About add_0_r.

(** Another common choice is to [Import] neither of them and use the [Nat.] and
    [Z.] prefixes as namespaces. This is a bit more verbose, but it is also
    easier to read. *)

(** What happens if module names themselves clash?
    We actually are already in that case: *)
About Nat.
About Coq.Init.Nat.

(** We have one module named [Nat] in [PeanoNat] and another one in the form
    of a library file in the [Init] directory.
    The name of the module [Coq.Init.Nat] was shadowed when we
    [Import]ed the module [Coq.Arith.PeanoNat].

    As we have just seen, it suffices to qualify more the module which is
    shadowed if we want to explicitly refer to it. *)

(** When two modules share the same name, there can be name clashes and
    shadowing if some of their constants have the same name. Let us illustrate
    it with nested modules.

    The situation would be similar if we required two library files with the
    same name in different libraries or directories (but we cannot illustrate
    this case conveniently in a single-file tutorial). *)

Module NestedABC1.
  Module ABC.
    Definition alice := 1.
    Definition bob := 1.
  End ABC.
End NestedABC1.

Module NestedABC2.
  Module ABC.
    Definition alice := 2.
    Definition charlie := 2.
  End ABC.
End NestedABC2.

(** For now, there is no ambiguity, since we have not imported any module.
    Our 4 new constants are:
    - [NestedABC1.ABC.alice]
    - [NestedABC1.ABC.bob]
    - [NestedABC2.ABC.alice]
    - [NestedABC2.ABC.charlie] *)
Locate alice.
Locate bob.
Locate charlie.

(** Now we [Import] both outer modules: *)
Import NestedABC1.
Print ABC.alice.
Print ABC.bob.

Import NestedABC2.

(** What are [ABC.alice], [ABC.bob] and [ABC.charlie] now? *)
Print ABC.alice.
Print ABC.bob.
Print ABC.charlie.

(** As we see, [ABC.alice] from [NestedABC1] has now been shadowed by
    [ABC.alice] in [NestedABC2]. Other than that, Coq is perfectly fine with
    [ABC.bob], which means that the [ABC] prefix in these three identifiers
    can actually refer to different modules.

    Of course, we can still refer to the [alice] constant in the first module
    with a more qualified identifier: *)
Locate alice.
Print NestedABC1.ABC.alice.

(** What happens if we [Import] both [ABC] momdules?
    Anything more than what we already saw: the order of the [Import] commands
    will determine the meaning of the short name [alice]. *)
Import NestedABC1.ABC.

(** The previous command did not shadow the module name [ABC] itself, so it
    still refers to the previously [Import]ed [NestedABC2.ABC] and we can
    [Import] it that way: *)
Import ABC.
Print alice.
Print bob.
Print charlie.

(** Where is the other [alice]? *)
Locate alice.
Print NestedABC1.ABC.alice.

(** To conclude this part, let us sum up what Coq allows and disallows regarding
    identifiers:
    - it is possible to have two files with the same name as long as they are
      in different directories;
    - it is possible to have two (non-file) modules with the same name as long
      as they are in different modules (which can be library files);
    - it is possible to have two constants with the same name as long as they
      are in different modules (including library files) *)

(** *** 1.4. Other content types in Modules *)

(** So far, our module [Foo] contained only definitions and lemmas.
    In practice there are many more content types in a module:
    - parameters and axioms
    - tactics
    - notations, abbreviations, [Ltac] notations and [Ltac2] notations
    - hints and type class instances
    - coercions
    - canonical structures

    It is not an issue if some (or all) these categories are obscure to you.
    We are only interested in what persists outside the module and in which
    case. We will only experiment with some of these categories. *)

Module Bar.
  (* A parameter: *)
  Parameter (secret : nat).
  (* An axiom: *)
  Axiom secret_is_42 : secret = 42.
  (* A custom tactic: *)
  Ltac find_secret := rewrite secret_is_42.
  (* An abbreviation: *)
  Notation add_42 := (Nat.add 42).
  (* A tactic notation: *)
  Tactic Notation "fs" := find_secret.
  (* A notation: *)
  Infix "+p" := Nat.add (only parsing, at level 30, right associativity) : nat_scope.
  (* Two lemmas: *)
  Lemma secret_42 : secret = 42.
  Proof. find_secret. reflexivity. Qed.
  Lemma baz : 21 +p 21 = secret.
  Proof. fs. reflexivity. Qed.
End Bar.

(** We have not imported [Bar] yet. What do we have? *)
About Bar.secret.
About Bar.secret_is_42.
Print Assumptions Bar.secret_is_42.
About Bar.secret_42.
Print Assumptions Bar.secret_42.
About Bar.baz.
Print Assumptions Bar.baz.

(** We see that parameters, axioms and lemmas are available, and axioms are
    treated as such after the end of the module.

    What about the other content? *)
Print Bar.add_42. (* Our abbreviation is available. *)
Fail Check (21 +p 21). (* Our notation is not. *)
Lemma forty_two : Bar.secret = 42.
Proof.
  Fail fs.
  Fail Bar.fs. (* Our tactic notation is not available. *)
  Bar.find_secret. (* But our tactic is. *)
  reflexivity.
Qed.

(** As we can see, only the _tactic_ `find_secret` and the _abbreviation_
    [add_42] were available. Now let's [Import Bar]: *)
Import Bar.
Check (21 +p 21).
Lemma forty_two' : secret = 42.
Proof.
  fs.
  reflexivity.
Qed.

(** To sum things up:
    - constants (i.e. parameters, definitions, lemmas, axioms, etc), tactics
      and abbreviations contained in a module are available even if we do not
      [Import] a module, with a qualified name;
    - notations, [Ltac] notations, [Ltac2] notations need the module to be
      imported to be available (note that notations are also associated to
      notation scopes we may have to [Open] or delimit with a key in order to
      use them)
    - the same holds for coercions, hints, type class instances and canonical
      structures (we omit the experiments for brevity). *)

(** *** 1.5 Guidelines about the order of [Require] and [Import] commands *)

(** We have seen that the order of [Require] and [Import] statements is
    important. Some constants could be shadowed by others, which can break
    definitions and proofs.

    In general, we should try to respect the following guidelines:
    - All [Require] commands should (ultimately) be at the beginning of a file,
      it makes it easier to know on which theories the file is built.
      It is fine during development to experiment temporarily with [Require]
      commands in the middle of the file and in a final version, either
      move the require statement at the beginning of a file, or the whole
      experiment in a separate file.
    - Usually, [Require] statements are actually [Require Import] statements:
      we want shorter names, notations, etc about theories we explicitly
      build on. Other constants which have been (implicitly) recursively
      [Require]d need a longer name to be used, so it is easier not to use them
      by accident (or to finally decide that we need to explicitly [Require
      Import] other modules).
    - We should [Require Import] only what is needed: it makes the global
      environment smaller, reduces the risks of shadowing and saves compilation
      time. In particular, breaking dependencies allows parallel compilation
      with multithreaded processors.
    - In general, we should [Require Import] files from external libraries first,
      in a more or less specialization order (the most basic theories first).
      Then, we should [Require Import] other internal library files at the end.
      Doing so prevents an external project to break our file by shadowing
      internal constants we use in that file.
    - We should try to [Require Import] files in the same order everytime to
      increase predictability of breakage due to shadowing. *)

(** ** 2. Fine control over module features *)

(** *** 2.1. On the user's side: selective import *)

(** Now is a good time to present a recent addition: selective import of
    modules. Recall that importing a module has basically two effects:
    - make the short names of constants (lemmas, definitions, ...),
      abbreviations and tactics available
    - enable the other content: notations, tactic notations, hints, coercions
      and canonical

    Selective import lets us precisely choose what we want to import. *)

(** To illustrate this, we create a hint database: *)
Create HintDb req_tut.

(** Our next example contains almost every categories of content: *)
Module Baz.
  (* Constants: *)
  Parameter b : nat.
  Definition almost_b := 41.
  Axiom b_rel : b = almost_b + 1.
  (* An abbreviation: *)
  Notation add_two := (fun x => x + 2).
  (* A tactic: *)
  Ltac rfl := reflexivity.
  (* A notation: *)
  Notation "x !!" := (x * 42) (at level 2) : nat_scope.
  (* A coercion: *)
  Coercion to_nat := fun (x : Z) => 42.
  (* A hint (please _do not_ pay attention to the [#[export]] locality
     attribute, it is here for compatibility reasons and will be discussed
     in the next section) *)
  #[export] Hint Rewrite b_rel : req_tut.
End Baz.

(** Let us import our notations first: *)
Import (notations) Baz.
Compute 10 !!.

(** Everything else has not been imported. *)
Fail Check b.
Fail Check almost_b.
Fail Check b_rel.
Fail Compute (0%Z + 3). (* Our coercion is not there. *)
Print HintDb req_tut. (* Our hint database is sadly empty. *)

(** Let us now import our coercions and hints with one command: *)
Import (coercions, hints) Baz.
Compute (0%Z + 3).
Print HintDb req_tut. (* Our hint is available *)
Lemma b_42 : Baz.b = 42.
Proof. autorewrite with req_tut. unfold Baz.almost_b. Baz.rfl. Qed.

(** Our notation is still there: *)
Compute 1 !!.

(** In fact, it is important to understand that there is no way to "un-import"
    anything in the same module or section. Once a module feature has been
    activated, it remains so until the end of the current section or module (or
    file), the only exception being shadowed content.

    We call the [coercions] and [notations] seen before _import categories_.
    The other import categories correspond to what we mentioned before, namely:
    [hints], [canonicals], [ltac.notations] and [ltac2.notations]. *)

(** We can also select which constants and abbreviations are available
    by their short names: *)
Import Baz(almost_b, b_rel, add_two).
Check almost_b.
Check b_rel.
Fail Check b.
Print add_two.
Fail Print rfl.
Print Baz.rfl.

(** There is also a way to tell Coq: [Import] everything except these
    categories. We just need to prepend them with a minus sign: *)
Module OtherBaz.
  Definition other_b := 42.
  Definition almost_other_b := 41.
  Definition almost_almost_other_b := 40.
  Notation "x ??" := (x * 42) (at level 2) : nat_scope.
  Coercion to_nat := fun (x : bool) => 42.
End OtherBaz.

Import -(coercions) OtherBaz.
Check almost_other_b.
Compute 10 ??.
Fail Check (true + 3).

(** Notice that, when we import everything except some categories, it is not
    possible, at the time of writing, to choose which identifiers are imported
    to be available as short names: they all are.

    We can always change our mind and decide to import a category we did not: *)
Import (coercions) OtherBaz.
Compute (true + 3).

(** To end this section, we turn to inductive types. *)
Module Unary.
  Inductive UnaryPos := one | successor (n : UnaryPos).
  Inductive UnaryZ := zero | plus (n : UnaryPos) | minus (n : UnaryPos).
End Unary.

(** We have not imported anything yet.
    Our inductive types and their constructors are available with their
    qualified names: *)
Check Unary.UnaryPos.
Check Unary.one.
Check Unary.UnaryZ.
Check Unary.minus.

(** So are our automatically generated induction principles (ending with
    [_sind], [_ind], [_rec] or [_rect]): *)
Check Unary.UnaryPos_rec.
Check Unary.UnaryZ_ind.

(** We can selectively [Import] all these constants and abbreviations.

    For an inductive type and its constructors, it suffices to give the type
    in the constants parenthesized list to be able to use its short name *)
Import Unary(UnaryPos).
Print UnaryPos.

(** However, its constructors and induction principles are not imported: *)
Check one. (* This is still Z.one *)
Fail Check UnaryPos_rec.

(** It is possible to [Import] them manually: *)
Import Unary(one, UnaryPos_rec).
Check one.
Check UnaryPos_rec.

(** But there is a shortcut: using [UnaryPos(..)] imports at once the type, as
    well as its constructors and induction principles: *)
Import Unary(UnaryPos(..)).
Check UnaryPos_ind.

(** The following command enables all short names associated to the inductive
    type [UnaryZ]: *)
Import Unary(UnaryZ(..)).
Check UnaryZ.
Check plus.
Check UnaryZ_ind.

(** ** 2.2. On the writer's side: locality attributes in modules *)

(** Let's now turn to a complementary tool to give control over what should
    remain local (if not hidden) and what should be exposed in a module (which
    can be a library file).

    Locality attributes change the visibility of content outside a section or
    a module. We're only interested in modules in this tutorial.

    Contrarily to selective import, which gives some amount of control on
    what is [Import]ed to _the user_ of a module, locality attributes lets _the
    writer_ of a module control what should be imported or not.

    There are 3 locality attributes: [#[local]], [#[export]] and [[#global]].

    The availability and effect of these attribute depends on each command (and
    even which Coq version we use) but, in short, when supported:
    - the [#[local]] attribute makes some content unavailable for import
    - the [#[export]] attribute makes some content available only if the module
      is [Import]ed
    - the [#[global]] attribute, in some cases, makes some content available
      outside the module even when not [Import]ed. *)

(** We experiment with our useless module [Baz]: *)

Module YetAnotherBaz.
  #[local] Definition yet_another_b := 42.
  Definition almost_yet_another_b := 41.
  #[local] Definition almost_almost_yet_another_b := 40.
  #[local] Notation "x %%" := (x * 42) (at level 2) : nat_scope.
  #[local] Coercion to_nat := fun (x : Prop) => 42.
  Compute 3 %%.
  Compute (True + 2).
End YetAnotherBaz.

Import YetAnotherBaz.
Fail Check yet_another_b.
Check YetAnotherBaz.yet_another_b.
Check almost_yet_another_b.
Fail Compute (True + 2).
(** The notation "x %%" is also unavailable, but we cannot show it without
    stopping compilation, as it is not even parsed.
    You can try it by uncommenting: *)
(** Compute 3 %%. *)

(** As we see, using the [#[local]] attribute in a module makes some content
    unavailable for import, which means, for constants, to make them only
    available with qualified names and for other categories (hints, coercions,
    etc), to disable them outside the module.

    This should be used without restraint on anything which should not be part
    of the user's interface, e.g. convenience ad-hoc tactics or unstable
    implementation details. *)

(** The [#[export]] attribute is not as well supported as [#[local]].
    In fact, in a module, since Coq 8.18, it is either not supported, or the
    default behavior (make a feature or short name available only when 
    a module is [Import]ed), except when used with the [Set] command which is
    used to change some Coq options.

    Prior to Coq 8.18, if one wants Hints to be available if (and only if) the
    module is [Import]ed, they should have the [#[export]] attribute and in
    Coq 8.17, Coq will emit a fatal warning they do not have any attribute.

    The following example shows what to expect (in any recent Coq version)
    when a Hint is kept local and a [Set] command has no attribute: *)
Module NotExported.
  Set Universe Polymorphism.
  #[local] Hint Rewrite Nat.add_1_r : req_tut.
  Test Universe Polymorphism.
End NotExported.

Import NotExported.

Lemma add_ones_r (n : nat) : n + 1 + 1 + 1 = S (S (S n)).
Proof.
  autorewrite with req_tut. (* This did _nothing_. *)
  rewrite 3!Nat.add_1_r.
  reflexivity.
Qed.

(** The option "Universe Polymorphism" is not set outside the module. *)
Test Universe Polymorphism.

(** Now, here is the same module with [#[export]] locality attributes: *)
Module Exported.
  #[export] Set Universe Polymorphism.
  Test Universe Polymorphism.
  #[export] Hint Rewrite Nat.add_1_r : req_tut.
End Exported.

Import Exported.

Lemma add_ones_r' (n : nat) : n + 1 + 1 + 1 = S (S (S n)).
Proof.
  autorewrite with req_tut.
  reflexivity.
Qed.

Test Universe Polymorphism.

(** As we saw, the [#[export]] locality attribute allowed us to [Set] our
    option whenever the module is [Import]ed.

    For our hint, [#[export]] is the default attribute since Coq 8.18, but if
    you need to work with older versions, you should add it to your Hints,
    if you want them to be available after import. *)

(** Now, for the [#[global]] setting. Again, it is often not supported and when
    it is, commands have the default behaviour (short names and features
    disabled except when the module is [Import]ed), except when [Set]ting
    options or with the [Hint] command (and typeclass instances): hints and
    settings with the [#[global]] attributes persist outside of the module,
    even if it is not [Import]ed. *)

(** Let us restore the state of the [Universe Polymorphism] option: *)
Unset Universe Polymorphism.
Test Universe Polymorphism.

Module SetGlobalExported.
  #[global] Set Universe Polymorphism.
  Test Universe Polymorphism.
  #[global] Hint Rewrite Nat.add_0_l Nat.add_0_r : req_tut.
  Lemma this_is_a_cool_lemma (n : nat) : 0 + n + 0 + 0 = 0 + n.
  Proof.
    autorewrite with req_tut.
    reflexivity.
  Qed.
End SetGlobalExported.

Test Universe Polymorphism.
(** We didn't even import the module, and the setting is already there!
    This should really be used with caution as it imposes our choice to any user
    who [Require]s our library file. *)

(** Our hints have also been silently added to our database, even without
    [Import]. Since hint databases have a tendency to make proofs very brittle
    this should also be used with caution. *)
Lemma this_is_a_cool_lemma (n : nat) : 0 + n + 0 + 0 = 0 + n.
Proof.
  autorewrite with req_tut.
  reflexivity.
Qed.
(** **** Exercise: why could we use the same name in the two previous lemmas? *)

(** ** 3. Exporting a module *)

(** Contrarily to [Require]d library files, module imports are not transitive.
    Consider the following nested module: *)
Module A.
  Definition this_is_a := 0.
  Module B.
    Definition this_is_b := 42.
  End B.
  Fail Check this_is_b.
  Import B.
  Check this_is_b.
End A.

(** This situation may seem contrived, but imagine rather a library file, say
    [A.v] which [Require]s and [Import]s another library file, say [B.v].
    At this point, we are in a situation similar to being in yet another file
    [C.v] which has [Require]d the file [A.v] (but not yet [Import]ed it). *)

(** We can access the content of [A] with qualified names. *)
Print A.this_is_a.
Print Module A.B.
Fail Print Module B.
Print A.B.this_is_b.
Fail Check A.this_is_b.
Fail Check this_is_b.

(** If we [Import A], we get short names for its content, including the module
    [B] itself. *)
Import A.
Print this_is_a.
Print Module B.

(** But, even though [B] is [Import]ed in [A], we cannot use a short name
    for [this_is_b]: *)
Fail Print this_is_b.
Print B.this_is_b.

(** This behaviour is actually very sane. Some programmers may have [Import]ed
    modules in library files for convenience, this should not affect every
    users of their library.

    Still, there is a way (and sometimes good reason) to both [Import] a module
    (which could be a file) and mark it for importation whenever the current
    module (or file) is [Import]ed: we use the [Export] command. *)
Module A'.
  Definition this_is_a' := 0.
  Module B'.
    Definition this_is_b' := 42.
  End B'.
  Fail Check this_is_b'. (* The module [B'] has not been [Import]ed in [A']. *)
  Export B'.
  Check this_is_b'. (* The module [B'] is now [Import]ed in A'. *)
End A'.

Fail Check this_is_b'.
Import A'.

(** Since [B'] was [Export]ed in [A'], [Import]ing [A'] also [Import]s [B']: *)
Check this_is_b'.

(** As this gives less control to the final user, [Export]ing modules should not
    be done lightly.

    A common usage is to write a library split in small library files and a
    summary file [Export]ing all of them, so that requiring and importing it
    makes all the library content available at once.

    Another use case is when [Import]ing a module (say about real numbers)
    would only really make sense when another one (say about integers) is also
    imported. *)

(** Other than that, [Export] behaves much like [Import]: it allows us to use
    short names for constants, activates module features such as [Hints],
    [Notations], etc.

    One can also use selective import with [Export], and locality attributes
    behave the same.

    Finally, it is possible to [Require] and [Export] a library file at the
    same time.
    For instance, the following command in [Coq.Arith.Arith_base]:
    [From Coq Require Export Arith.PeanoNat.]
    imports [PeanoNat]'s content in [Coq.Arith.Arith_base] as well as in any
    file which [Require]s and [Import]s (or [Export]s) [Coq.Arith.Arith_base].
*)
