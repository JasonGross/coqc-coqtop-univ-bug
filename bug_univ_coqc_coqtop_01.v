(* -*- coq-prog-args: ("-emacs" "-indices-matter") -*- *)
(* File reduced by coq-bug-finder from original input, then from 8353 lines to 4738 lines *)
(* coqc version trunk (October 2014) compiled on Oct 20 2014 8:41:32 with OCaml 3.12.1
   coqtop version trunk (October 2014) *)
Module Export Datatypes.
Set Implicit Arguments.


Global Set Universe Polymorphism.
Global Set Asymmetric Patterns.
Local Set Primitive Projections.
Global Set Nonrecursive Elimination Schemes.
Local Unset Elimination Schemes.

(** [option A] is the extension of [A] with an extra element [None] *)

Inductive option (A : Type) : Type :=
  | Some : A -> option A
  | None : option A.

Scheme option_rect := Induction for option Sort Type.

Arguments None [A].

(** [sum A B], written [A + B], is the disjoint sum of [A] and [B] *)

Inductive sum (A B : Type) : Type :=
  | inl : A -> sum A B
  | inr : B -> sum A B.

Scheme sum_rect := Induction for sum Sort Type.

Notation "x + y" := (sum x y) : type_scope.

Arguments inl {A B} _ , [A] B _.
Arguments inr {A B} _ , A [B] _.

Notation "A \/ B" := (A + B)%type (only parsing) : type_scope.
Notation or := sum (only parsing).

(** [prod A B], written [A * B], is the product of [A] and [B];
    the pair [pair A B a b] of [a] and [b] is abbreviated [(a,b)] *)

Record prod (A B : Type) := pair { fst : A ; snd : B }.

Scheme prod_rect := Induction for prod Sort Type.

Arguments pair {A B} _ _.
Arguments fst {A B} _ / .
Arguments snd {A B} _ / .

Add Printing Let prod.

Notation "x * y" := (prod x y) : type_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.
Notation "A /\ B" := (prod A B) (only parsing) : type_scope.
Notation and := prod (only parsing).
Notation conj := pair (only parsing).

Hint Resolve pair inl inr : core.

Definition prod_curry (A B C : Type) (f : A -> B -> C)
  (p : prod A B) : C := f (fst p) (snd p).

(** [iff A B], written [A <-> B], expresses the equivalence of [A] and [B] *)

Definition iff (A B : Type) := prod (A -> B) (B -> A).

Notation "A <-> B" := (iff A B) : type_scope.

(* Natural numbers. *)



(** [identity A a] is the family of datatypes on [A] whose sole non-empty
    member is the singleton datatype [identity A a a] whose
    sole inhabitant is denoted [refl_identity A a] *)

Inductive identity (A : Type) (a : A) : A -> Type :=
  identity_refl : identity a a.

Scheme identity_rect := Induction for identity Sort Type.

Hint Resolve identity_refl: core.

Arguments identity {A} _ _.
Arguments identity_refl {A a} , [A] a.

Arguments identity_rect [A] a P f y i.


(** Identity type *)

(*
Definition ID := forall A : Type, A -> A.
Definition id : ID := fun A x => x.
*)

Delimit Scope identity_scope with identity.

Notation "x = y :> A" := (@identity A x y)%identity : identity_scope.

Notation "x = y" := (x = y :>_)%identity : identity_scope.
Notation "x <> y  :> T" := (~ x = y :>T)%identity : identity_scope.
Notation "x <> y" := (x <> y :>_)%identity : identity_scope.

Local Open Scope identity_scope.

(** Another way of interpreting booleans as propositions *)

(* Definition is_true b := b = true. *)

(** Polymorphic lists and some operations *)

Inductive list (A : Type) : Type :=
 | nil : list A
 | cons : A -> list A -> list A.

Scheme list_rect := Induction for list Sort Type.

Arguments nil [A].
Infix "::" := cons (at level 60, right associativity) : list_scope.
Delimit Scope list_scope with list.
Bind Scope list_scope with list.

Local Open Scope list_scope.
(** Concatenation of two lists *)

Definition app (A : Type) : list A -> list A -> list A :=
  fix app l m :=
  match l with
   | nil => m
   | a :: l1 => a :: app l1 m
  end.

Infix "++" := app (right associativity, at level 60) : list_scope.
End Datatypes.
Module Export Specif.
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(************************************************************************)
(*   This file has been modified for the purposes of the HoTT library.  *)
(************************************************************************)

(** Basic specifications : sets that may contain logical information *)

Set Implicit Arguments.

Local Open Scope identity_scope.
Local Set Primitive Projections.
Local Unset Elimination Schemes.

(** [(sig A P)], or more suggestively [{x:A & (P x)}] is a Sigma-type.
    Similarly for [(sig2 A P Q)], also written [{x:A & (P x) & (Q x)}]. *)

Record sig {A} (P : A -> Type) := exist { proj1_sig : A ; proj2_sig : P proj1_sig }.

Scheme sig_rect := Induction for sig Sort Type.

(** We make the parameters maximally inserted so that we can pass around [pr1] as a function and have it actually mean "first projection" in, e.g., [ap]. *)

Arguments exist {A}%type P%type _ _.
Arguments proj1_sig {A P} _ / .
Arguments proj2_sig {A P} _ / .

Inductive sig2 (A:Type) (P Q:A -> Type) : Type :=
    exist2 : forall x:A, P x -> Q x -> sig2 P Q.

Scheme sig2_rect := Induction for sig2 Sort Type.

Arguments sig (A P)%type.
Arguments sig2 (A P Q)%type.

(** *** Notations *)

(** In standard Coq, [sig] and [sig2] are defined as "subset types" which sum over predicates [P:A->Prop], while [sigT] and [sigT2] are the [Type] variants.  Because we don't use [Prop], we combine the two versions, and make [sigT] a notation for [sig].  Note that some parts of Coq (like [Program Definition]) expect [sig] to be present. *)

Notation sigT := sig (only parsing).
Notation existT := exist (only parsing).
Notation sigT_rect := sig_rect (only parsing).
Notation sigT_rec := sig_rect (only parsing).
Notation sigT_ind := sig_rect (only parsing).
Notation sigT2 := sig2 (only parsing).
Notation existT2 := exist2 (only parsing).
Notation sigT2_rect := sig2_rect (only parsing).
Notation sigT2_rec := sig2_rect (only parsing).
Notation sigT2_ind := sig2_rect (only parsing).

Notation  ex_intro := existT (only parsing).

Notation "{ x | P }" := (sigT (fun x => P)) : type_scope.
Notation "{ x | P & Q }" := (sigT2 (fun x => P) (fun x => Q)) : type_scope.
Notation "{ x : A | P }" := (sigT (fun x:A => P)) : type_scope.
Notation "{ x : A | P & Q }" := (sigT2 (fun x:A => P) (fun x:A => Q)) :
  type_scope.

Notation "'exists' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Notation "'exists2' x , p & q" := (sigT2 (fun x => p) (fun x => q))
  (at level 200, x ident, p at level 200, right associativity) : type_scope.
Notation "'exists2' x : t , p & q" := (sigT2 (fun x:t => p) (fun x:t => q))
  (at level 200, x ident, t at level 200, p at level 200, right associativity,
    format "'[' 'exists2'  '/  ' x  :  t ,  '/  ' '[' p  &  '/' q ']' ']'")
  : type_scope.

(* Definition exist := existT.  (* (only parsing). *) *)
(* Definition sig := sigT.  (* (only parsing). *) *)
(* Notation sig2 := (@sigT2 _) (only parsing). *)
(* Notation exist2 := (@existT2 _) (only parsing). *)

Notation "{ x : A  & P }" := (sigT (fun x:A => P)) : type_scope.
Notation "{ x : A  & P  & Q }" := (sigT2 (fun x:A => P) (fun x:A => Q)) :
  type_scope.
(* Notation "{ x & P }" := (sigT (fun x:_ => P)) : type_scope. *)
(* Notation "{ x & P  & Q }" := (sigT2 (fun x:_ => P) (fun x:A => Q)) : *)
(*   type_scope. *)

Add Printing Let sig.
Add Printing Let sig2.


(** Projections of [sigT]

    An element [x] of a sigma-type [{y:A & P y}] is a dependent pair
    made of an [a] of type [A] and an [h] of type [P a].  Then,
    [(proj1 x)] is the first projection and [(proj2 x)] is the
    second projection, the type of which depends on the [proj1]. *)

Notation projT1 := proj1_sig (only parsing).
Notation projT2 := proj2_sig (only parsing).


(** Various forms of the axiom of choice for specifications *)

Section Choice_lemmas.

  Variables S S' : Type.
  Variable R : S -> S' -> Type.
  Variable R' : S -> S' -> Type.
  Variables R1 R2 : S -> Type.

  Lemma Choice :
   (forall x:S, {y:S' & R' x y}) -> {f:S -> S' & forall z:S, R' z (f z)}.
  Proof.
    intro H.
    exists (fun z => projT1 (H z)).
    intro z; destruct (H z); assumption.
  Defined.

(*
  Lemma bool_choice :
   (forall x:S, (R1 x) + (R2 x)) ->
     {f:S -> bool & forall x:S, (f x = true) * (R1 x) + (f x = false) * R2 x}.
  Proof.
    intro H.
    exists (fun z:S => if H z then true else false).
    intro z; destruct (H z); auto.
  Defined.
*)

End Choice_lemmas.

Section Dependent_choice_lemmas.

  Variables X : Type.
  Variable R : X -> X -> Type.

End Dependent_choice_lemmas.


 (** A result of type [(Exc A)] is either a normal value of type [A] or
     an [error] :

     [Inductive Exc [A:Type] : Type := value : A->(Exc A) | error : (Exc A)].

     It is implemented using the option type. *)

Definition Exc := option.
Definition value := Some.
Definition error := @None.

Arguments error [A].

Definition except := False_rec. (* for compatibility with previous versions *)

Arguments except [P] _.

Theorem absurd_set : forall (A:Prop) (C:Set), A -> ~ A -> C.
Proof.
  intros A C h1 h2.
  apply False_rec.
  apply (h2 h1).
Defined.

Hint Resolve existT existT2: core.


(* Compatibility with ssreflect *)

(* Notation sigS := sigT (compat "8.2"). *)
Notation existS := existT (compat "8.2").
(* Notation sigS_rect := sigT_rect (compat "8.2"). *)
(* Notation sigS_rec := sigT_rec (compat "8.2"). *)
(* Notation sigS_ind := sigT_ind (compat "8.2"). *)
Notation projS1 := projT1 (compat "8.2").
Notation projS2 := projT2 (compat "8.2").

(* Notation sigS2 := sigT2 (compat "8.2"). *)
(* Notation existS2 := existT2 (compat "8.2"). *)
(* Notation sigS2_rect := sigT2_rect (compat "8.2"). *)
(* Notation sigS2_rec := sigT2_rec (compat "8.2"). *)
(* Notation sigS2_ind := sigT2_ind (compat "8.2"). *)
End Specif.
Open Scope type_scope.
Module Export HoTT_DOT_Basics_DOT_Overture.
Module Export HoTT.
Module Export Basics.
Module Export Overture.


Local Unset Elimination Schemes.

Definition relation (A : Type) := A -> A -> Type.

Class Reflexive {A} (R : relation A) :=
  reflexivity : forall x : A, R x x.

Class Symmetric {A} (R : relation A) :=
  symmetry : forall x y, R x y -> R y x.

Class Transitive {A} (R : relation A) :=
  transitivity : forall x y z, R x y -> R y z -> R x z.


Class PreOrder {A} (R : relation A) :=
  { PreOrder_Reflexive : Reflexive R | 2 ;
    PreOrder_Transitive : Transitive R | 2 }.

Global Existing Instance PreOrder_Reflexive.
Global Existing Instance PreOrder_Transitive.
Arguments transitivity {A R _} / {_ _ _} _ _.




Ltac symmetry :=
  let R := match goal with |- ?R ?x ?y => constr:(R) end in
  let x := match goal with |- ?R ?x ?y => constr:(x) end in
  let y := match goal with |- ?R ?x ?y => constr:(y) end in
  let pre_proof_term_head := constr:(@symmetry _ R _) in
  let proof_term_head := (eval cbn in pre_proof_term_head) in
  refine (proof_term_head y x _); change (R y x).

Tactic Notation "etransitivity" open_constr(y) :=
  let R := match goal with |- ?R ?x ?z => constr:(R) end in
  let x := match goal with |- ?R ?x ?z => constr:(x) end in
  let z := match goal with |- ?R ?x ?z => constr:(z) end in
  let pre_proof_term_head := constr:(@transitivity _ R _) in
  let proof_term_head := (eval cbn in pre_proof_term_head) in
  refine (proof_term_head x y z _ _); [ change (R x y) | change (R y z) ].

Tactic Notation "etransitivity" := etransitivity _.




Notation Type0 := Set.

Definition Type1 := Eval hnf in let U := Type in let gt := (Set : U) in U.
Identity Coercion unfold_Type1 : Type1 >-> Sortclass.


Notation idmap := (fun x => x).


Definition const {A B} (b : B) := fun x : A => b.


Notation "( x ; y )" := (existT _ x y) : fibration_scope.
Open Scope fibration_scope.


Notation pr1 := projT1.
Notation pr2 := projT2.


Notation "x .1" := (pr1 x) (at level 3, format "x '.1'") : fibration_scope.
Notation "x .2" := (pr2 x) (at level 3, format "x '.2'") : fibration_scope.


Definition compose {A B C : Type} (g : B -> C) (f : A -> B) :=
  fun x => g (f x).


Notation "g 'o' f" := (compose g f) (at level 40, left associativity) : function_scope.
Open Scope function_scope.


Definition composeD {A B C} (g : forall b, C b) (f : A -> B) := fun x : A => g (f x).

Notation "g 'oD' f" := (composeD g f) (at level 40, left associativity) : function_scope.






Inductive paths {A : Type} (a : A) : A -> Type :=
  idpath : paths a a.

Arguments idpath {A a} , [A] a.

Scheme paths_ind := Induction for paths Sort Type.
Arguments paths_ind [A] a P f y p.


Definition paths_rect := paths_ind.

Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.



Definition paths_ind' {A : Type} (P : forall (a b : A), (a = b) -> Type)
  : (forall (a : A), P a a idpath) -> forall (a b : A) (p : a = b), P a b p.
Proof.
  intros H ? ? [].
  apply H.
Defined.



Delimit Scope path_scope with path.
Local Open Scope path_scope.
Definition inverse {A : Type} {x y : A} (p : x = y) : y = x. exact (match p with idpath => idpath end). Defined.
Global Instance symmetric_paths {A} : Symmetric (@paths A) | 0.
admit.
Defined.





Definition concat {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z :=
  match p, q with idpath, idpath => idpath end.


Arguments concat {A x y z} p q : simpl nomatch.
Global Instance transitive_paths {A} : Transitive (@paths A) | 0. exact (@concat A). Defined.
Arguments transitive_paths / .




Notation "1" := idpath : path_scope.


Notation "p @ q" := (concat p q) (at level 20) : path_scope.


Notation "p ^" := (inverse p) (at level 3, format "p '^'") : path_scope.
Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y. exact (match p with idpath => u end). Defined.

Notation "p # x" := (transport _ p x) (right associativity, at level 65, only parsing) : path_scope.
Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y. exact (match p with idpath => idpath end). Defined.



Notation ap01 := ap (only parsing).

Definition pointwise_paths {A} {P:A->Type} (f g:forall x:A, P x)
  := forall x:A, f x = g x.

Hint Unfold pointwise_paths : typeclass_instances.

Notation "f == g" := (pointwise_paths f g) (at level 70, no associativity) : type_scope.
Definition apD10 {A} {B:A->Type} {f g : forall x, B x} (h:f=g)
  : f == g. exact (fun x => match h with idpath => 1 end). Defined.
Definition ap10 {A B} {f g:A->B} (h:f=g) : f == g. exact (apD10 h). Defined.

Definition ap11 {A B} {f g:A->B} (h:f=g) {x y:A} (p:x=y) : f x = g y.
Proof.
  case h, p; reflexivity.
Defined.



Definition apD {A:Type} {B:A->Type} (f:forall a:A, B a) {x y:A} (p:x=y):
  p # (f x) = f y
  :=
  match p with idpath => idpath end.








Definition Sect {A B : Type} (s : A -> B) (r : B -> A) :=
  forall x : A, r (s x) = x.


Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv {
  equiv_inv : B -> A ;
  eisretr : Sect equiv_inv f;
  eissect : Sect f equiv_inv;
  eisadj : forall x : A, eisretr (f x) = ap f (eissect x)
}.

Arguments eisretr {A B} f {_} _.
Arguments eissect {A B} f {_} _.
Arguments eisadj {A B} f {_} _.


Record Equiv A B := BuildEquiv {
  equiv_fun : A -> B ;
  equiv_isequiv : IsEquiv equiv_fun
}.

Coercion equiv_fun : Equiv >-> Funclass.

Global Existing Instance equiv_isequiv.

Delimit Scope equiv_scope with equiv.
Local Open Scope equiv_scope.

Notation "A <~> B" := (Equiv A B) (at level 85) : equiv_scope.



Notation "f ^-1" := (@equiv_inv _ _ f _) (at level 3, format "f '^-1'") : equiv_scope.










Class Contr_internal (A : Type) := BuildContr {
  center : A ;
  contr : (forall y : A, center = y)
}.

Arguments center A {_}.





Inductive trunc_index : Type :=
| minus_two : trunc_index
| trunc_S : trunc_index -> trunc_index.

Scheme trunc_index_ind := Induction for trunc_index Sort Type.


Definition trunc_index_rect := trunc_index_ind.


Delimit Scope trunc_scope with trunc.
Bind Scope trunc_scope with trunc_index.



Notation "n .+1" := (trunc_S n) (at level 2, left associativity, format "n .+1") : trunc_scope.
Notation "n .+1" := (S n) (at level 2, left associativity, format "n .+1") : nat_scope.
Notation "n .+2" := (n.+1.+1)%trunc (at level 2, left associativity, format "n .+2") : trunc_scope.
Notation "n .+2" := (n.+1.+1)%nat (at level 2, left associativity, format "n .+2") : nat_scope.
Local Open Scope trunc_scope.
Notation "-2" := minus_two (at level 0) : trunc_scope.
Notation "-1" := (-2.+1) (at level 0) : trunc_scope.
Notation "0" := (-1.+1) : trunc_scope.

Fixpoint IsTrunc_internal (n : trunc_index) (A : Type) : Type :=
  match n with
    | -2 => Contr_internal A
    | n'.+1 => forall (x y : A), IsTrunc_internal n' (x = y)
  end.

Class IsTrunc (n : trunc_index) (A : Type) : Type :=
  Trunc_is_trunc : IsTrunc_internal n A.
Global Instance istrunc_paths (A : Type) n `{H : IsTrunc n.+1 A} (x y : A)
: IsTrunc n (x = y).
admit.
Defined.


Hint Extern 0 => progress change IsTrunc_internal with IsTrunc in * : typeclass_instances.

Notation Contr := (IsTrunc -2).
Notation IsHProp := (IsTrunc -1).
Notation IsHSet := (IsTrunc 0).

Hint Extern 0 => progress change Contr_internal with Contr in * : typeclass_instances.





Monomorphic Axiom dummy_funext_type : Type0.
Monomorphic Class Funext := { dummy_funext_value : dummy_funext_type }.
Axiom isequiv_apD10 : forall `{Funext} (A : Type) (P : A -> Type) f g, IsEquiv (@apD10 A P f g).
Definition path_forall `{Funext} {A : Type} {P : A -> Type} (f g : forall x : A, P x) :
  f == g -> f = g. exact ((@apD10 A P f g)^-1). Defined.






Hint Resolve
  @idpath @inverse
 : path_hints.

Hint Resolve @idpath : core.


Inductive Empty : Type1 := .
Definition not (A:Type) : Type. exact (A -> Empty). Defined.
Notation "~ x" := (not x) : type_scope.
Definition complement {A} (R : relation A) : relation A. exact (fun x y => ~ (R x y)). Defined.

Typeclasses Opaque complement.

Class Irreflexive {A} (R : relation A) :=
  irreflexivity : Reflexive (complement R).


Inductive Unit : Type1 :=
    tt : Unit.

Scheme Unit_ind := Induction for Unit Sort Type.
Scheme Unit_rec := Minimality for Unit Sort Type.
Definition Unit_rect := Unit_ind.




Class Decidable (A : Type) :=
  dec : A + (~ A).
Arguments dec A {_}.

Class DecidablePaths (A : Type) :=
  dec_paths : forall (x y : A), Decidable (x = y).
Global Existing Instance dec_paths.




Class IsPointed (A : Type) := point : A.
Definition pointedType := { u : Type & IsPointed u }.
Arguments point A {_}.





Definition hfiber {A B : Type} (f : A -> B) (y : B) := { x : A & f x = y }.


Ltac done :=
  trivial; intros; solve
    [ repeat first
      [ solve [trivial]
      | solve [symmetry; trivial]
      | reflexivity


      | contradiction
      | split ]
    | match goal with
      H : ~ _ |- _ => solve [destruct H; trivial]
      end ].
Tactic Notation "by" tactic(tac) :=
  tac; done.


Tactic Notation "test" tactic3(tac) :=
  try (first [ tac | fail 2 tac "does not succeed" ]; fail tac "succeeds"; [] ).


Tactic Notation "not" tactic3(tac) := try ((test tac); fail 1 tac "succeeds").


Ltac path_induction :=
  intros; repeat progress (
    match goal with
      | [ p : ?x = ?y  |- _ ] => not constr_eq x y; induction p
    end
  ).

End Overture.

End Basics.

End HoTT.

End HoTT_DOT_Basics_DOT_Overture.
Import HoTT_DOT_Basics_DOT_Overture.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.Basics.

Import HoTT_DOT_Basics_DOT_Overture.HoTT.Basics.Overture.

Local Open Scope path_scope.






Definition concat_p1 {A : Type} {x y : A} (p : x = y) :
  p @ 1 = p
  :=
  match p with idpath => 1 end.


Definition concat_1p {A : Type} {x y : A} (p : x = y) :
  1 @ p = p
  :=
  match p with idpath => 1 end.


Definition concat_p_pp {A : Type} {x y z t : A} (p : x = y) (q : y = z) (r : z = t) :
  p @ (q @ r) = (p @ q) @ r :=
  match r with idpath =>
    match q with idpath =>
      match p with idpath => 1
      end end end.

Definition concat_pp_p {A : Type} {x y z t : A} (p : x = y) (q : y = z) (r : z = t) :
  (p @ q) @ r = p @ (q @ r) :=
  match r with idpath =>
    match q with idpath =>
      match p with idpath => 1
      end end end.


Definition concat_pV {A : Type} {x y : A} (p : x = y) :
  p @ p^ = 1
  :=
  match p with idpath => 1 end.


Definition concat_Vp {A : Type} {x y : A} (p : x = y) :
  p^ @ p = 1
  :=
  match p with idpath => 1 end.



Definition concat_V_pp {A : Type} {x y z : A} (p : x = y) (q : y = z) :
  p^ @ (p @ q) = q
  :=
  match q with idpath =>
    match p with idpath => 1 end
  end.

Definition concat_p_Vp {A : Type} {x y z : A} (p : x = y) (q : x = z) :
  p @ (p^ @ q) = q
  :=
  match q with idpath =>
    match p with idpath => 1 end
  end.

Definition concat_pp_V {A : Type} {x y z : A} (p : x = y) (q : y = z) :
  (p @ q) @ q^ = p
  :=
  match q with idpath =>
    match p with idpath => 1 end
  end.

Definition concat_pV_p {A : Type} {x y z : A} (p : x = z) (q : y = z) :
  (p @ q^) @ q = p
  :=
  (match q as i return forall p, (p @ i^) @ i = p with
    idpath =>
    fun p =>
      match p with idpath => 1 end
  end) p.


Definition inv_pp {A : Type} {x y z : A} (p : x = y) (q : y = z) :
  (p @ q)^ = q^ @ p^
  :=
  match q with idpath =>
    match p with idpath => 1 end
  end.

Definition inv_Vp {A : Type} {x y z : A} (p : y = x) (q : y = z) :
  (p^ @ q)^ = q^ @ p
  :=
  match q with idpath =>
    match p with idpath => 1 end
  end.

Definition inv_pV {A : Type} {x y z : A} (p : x = y) (q : z = y) :
  (p @ q^)^ = q @ p^.
Proof.
  destruct p.
destruct q.
reflexivity.
Defined.

Definition inv_VV {A : Type} {x y z : A} (p : y = x) (q : z = y) :
  (p^ @ q^)^ = q @ p.
Proof.
  destruct p.
destruct q.
reflexivity.
Defined.


Definition inv_V {A : Type} {x y : A} (p : x = y) :
  p^^ = p
  :=
  match p with idpath => 1 end.



Definition moveR_Mp {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x) :
  p = r^ @ q -> r @ p = q.
Proof.
  destruct r.
  intro h.
exact (concat_1p _ @ h @ concat_1p _).
Defined.

Definition moveR_pM {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x) :
  r = q @ p^ -> r @ p = q.
Proof.
  destruct p.
  intro h.
exact (concat_p1 _ @ h @ concat_p1 _).
Defined.

Definition moveR_Vp {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y) :
  p = r @ q -> r^ @ p = q.
Proof.
  destruct r.
  intro h.
exact (concat_1p _ @ h @ concat_1p _).
Defined.

Definition moveR_pV {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x) :
  r = q @ p -> r @ p^ = q.
Proof.
  destruct p.
  intro h.
exact (concat_p1 _ @ h @ concat_p1 _).
Defined.

Definition moveL_Mp {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x) :
  r^ @ q = p -> q = r @ p.
Proof.
  destruct r.
  intro h.
exact ((concat_1p _)^ @ h @ (concat_1p _)^).
Defined.

Definition moveL_pM {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x) :
  q @ p^ = r -> q = r @ p.
Proof.
  destruct p.
  intro h.
exact ((concat_p1 _)^ @ h @ (concat_p1 _)^).
Defined.

Definition moveL_Vp {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y) :
  r @ q = p -> q = r^ @ p.
Proof.
  destruct r.
  intro h.
exact ((concat_1p _)^ @ h @ (concat_1p _)^).
Defined.

Definition moveL_pV {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x) :
  q @ p = r -> q = r @ p^.
Proof.
  destruct p.
  intro h.
exact ((concat_p1 _)^ @ h @ (concat_p1 _)^).
Defined.

Definition moveL_1M {A : Type} {x y : A} (p q : x = y) :
  p @ q^ = 1 -> p = q.
Proof.
  destruct q.
  intro h.
exact ((concat_p1 _)^ @ h).
Defined.

Definition moveL_M1 {A : Type} {x y : A} (p q : x = y) :
  q^ @ p = 1 -> p = q.
Proof.
  destruct q.
  intro h.
exact ((concat_1p _)^ @ h).
Defined.

Definition moveL_1V {A : Type} {x y : A} (p : x = y) (q : y = x) :
  p @ q = 1 -> p = q^.
Proof.
  destruct q.
  intro h.
exact ((concat_p1 _)^ @ h).
Defined.

Definition moveL_V1 {A : Type} {x y : A} (p : x = y) (q : y = x) :
  q @ p = 1 -> p = q^.
Proof.
  destruct q.
  intro h.
exact ((concat_1p _)^ @ h).
Defined.

Definition moveR_M1 {A : Type} {x y : A} (p q : x = y) :
  1 = p^ @ q -> p = q.
Proof.
  destruct p.
  intro h.
exact (h @ (concat_1p _)).
Defined.

Definition moveR_1M {A : Type} {x y : A} (p q : x = y) :
  1 = q @ p^ -> p = q.
Proof.
  destruct p.
  intro h.
exact (h @ (concat_p1 _)).
Defined.

Definition moveR_1V {A : Type} {x y : A} (p : x = y) (q : y = x) :
  1 = q @ p -> p^ = q.
Proof.
  destruct p.
  intro h.
exact (h @ (concat_p1 _)).
Defined.

Definition moveR_V1 {A : Type} {x y : A} (p : x = y) (q : y = x) :
  1 = p @ q -> p^ = q.
Proof.
  destruct p.
  intro h.
exact (h @ (concat_1p _)).
Defined.

Definition moveR_transport_p {A : Type} (P : A -> Type) {x y : A}
  (p : x = y) (u : P x) (v : P y)
  : u = p^ # v -> p # u = v.
Proof.
  destruct p.
  exact idmap.
Defined.

Definition moveR_transport_V {A : Type} (P : A -> Type) {x y : A}
  (p : y = x) (u : P x) (v : P y)
  : u = p # v -> p^ # u = v.
Proof.
  destruct p.
  exact idmap.
Defined.

Definition moveL_transport_V {A : Type} (P : A -> Type) {x y : A}
  (p : x = y) (u : P x) (v : P y)
  : p # u = v -> u = p^ # v.
Proof.
  destruct p.
  exact idmap.
Defined.

Definition moveL_transport_p {A : Type} (P : A -> Type) {x y : A}
  (p : y = x) (u : P x) (v : P y)
  : p^ # u = v -> u = p # v.
Proof.
  destruct p.
  exact idmap.
Defined.
Definition ap_1 {A B : Type} (x : A) (f : A -> B) :
  ap f 1 = 1 :> (f x = f x).
admit.
Defined.
Definition apD_1 {A B} (x : A) (f : forall x : A, B x) :
  apD f 1 = 1 :> (f x = f x).
admit.
Defined.


Definition ap_pp {A B : Type} (f : A -> B) {x y z : A} (p : x = y) (q : y = z) :
  ap f (p @ q) = (ap f p) @ (ap f q)
  :=
  match q with
    idpath =>
    match p with idpath => 1 end
  end.

Definition ap_p_pp {A B : Type} (f : A -> B) {w : B} {x y z : A}
  (r : w = f x) (p : x = y) (q : y = z) :
  r @ (ap f (p @ q)) = (r @ ap f p) @ (ap f q).
Proof.
  destruct p, q.
simpl.
exact (concat_p_pp r 1 1).
Defined.

Definition ap_pp_p {A B : Type} (f : A -> B) {x y z : A} {w : B}
  (p : x = y) (q : y = z) (r : f z = w) :
  (ap f (p @ q)) @ r = (ap f p) @ (ap f q @ r).
Proof.
  destruct p, q.
simpl.
exact (concat_pp_p 1 1 r).
Defined.


Definition inverse_ap {A B : Type} (f : A -> B) {x y : A} (p : x = y) :
  (ap f p)^ = ap f (p^)
  :=
  match p with idpath => 1 end.

Definition ap_V {A B : Type} (f : A -> B) {x y : A} (p : x = y) :
  ap f (p^) = (ap f p)^
  :=
  match p with idpath => 1 end.



Definition ap_idmap {A : Type} {x y : A} (p : x = y) :
  ap idmap p = p
  :=
  match p with idpath => 1 end.

Definition ap_compose {A B C : Type} (f : A -> B) (g : B -> C) {x y : A} (p : x = y) :
  ap (g o f) p = ap g (ap f p)
  :=
  match p with idpath => 1 end.


Definition ap_compose' {A B C : Type} (f : A -> B) (g : B -> C) {x y : A} (p : x = y) :
  ap (fun a => g (f a)) p = ap g (ap f p)
  :=
  match p with idpath => 1 end.


Definition ap_const {A B : Type} {x y : A} (p : x = y) (z : B) :
  ap (fun _ => z) p = 1
  :=
  match p with idpath => idpath end.


Definition concat_Ap {A B : Type} {f g : A -> B} (p : forall x, f x = g x) {x y : A} (q : x = y) :
  (ap f q) @ (p y) = (p x) @ (ap g q)
  :=
  match q with
    | idpath => concat_1p _ @ ((concat_p1 _) ^)
  end.


Definition concat_A1p {A : Type} {f : A -> A} (p : forall x, f x = x) {x y : A} (q : x = y) :
  (ap f q) @ (p y) = (p x) @ q
  :=
  match q with
    | idpath => concat_1p _ @ ((concat_p1 _) ^)
  end.
Definition concat_pA1 {A : Type} {f : A -> A} (p : forall x, x = f x) {x y : A} (q : x = y) :
  (p x) @ (ap f q) =  q @ (p y). exact (match q as i in (_ = y) return (p x @ ap f i = i @ p y) with
    | idpath => concat_p1 _ @ (concat_1p _)^
  end). Defined.


Definition concat_pA_pp {A B : Type} {f g : A -> B} (p : forall x, f x = g x)
  {x y : A} (q : x = y)
  {w z : B} (r : w = f x) (s : g y = z)
  :
  (r @ ap f q) @ (p y @ s) = (r @ p x) @ (ap g q @ s).
Proof.
  destruct q, s; simpl.
  repeat rewrite concat_p1.
  reflexivity.
Defined.

Definition concat_pA_p {A B : Type} {f g : A -> B} (p : forall x, f x = g x)
  {x y : A} (q : x = y)
  {w : B} (r : w = f x)
  :
  (r @ ap f q) @ p y = (r @ p x) @ ap g q.
Proof.
  destruct q; simpl.
  repeat rewrite concat_p1.
  reflexivity.
Defined.

Definition concat_A_pp {A B : Type} {f g : A -> B} (p : forall x, f x = g x)
  {x y : A} (q : x = y)
  {z : B} (s : g y = z)
  :
  (ap f q) @ (p y @ s) = (p x) @ (ap g q @ s).
Proof.
  destruct q, s; cbn.
  repeat rewrite concat_p1, concat_1p.
  reflexivity.
Defined.

Definition concat_pA1_pp {A : Type} {f : A -> A} (p : forall x, f x = x)
  {x y : A} (q : x = y)
  {w z : A} (r : w = f x) (s : y = z)
  :
  (r @ ap f q) @ (p y @ s) = (r @ p x) @ (q @ s).
Proof.
  destruct q, s; simpl.
  repeat rewrite concat_p1.
  reflexivity.
Defined.

Definition concat_pp_A1p {A : Type} {g : A -> A} (p : forall x, x = g x)
  {x y : A} (q : x = y)
  {w z : A} (r : w = x) (s : g y = z)
  :
  (r @ p x) @ (ap g q @ s) = (r @ q) @ (p y @ s).
Proof.
  destruct q, s; simpl.
  repeat rewrite concat_p1.
  reflexivity.
Defined.

Definition concat_pA1_p {A : Type} {f : A -> A} (p : forall x, f x = x)
  {x y : A} (q : x = y)
  {w : A} (r : w = f x)
  :
  (r @ ap f q) @ p y = (r @ p x) @ q.
Proof.
  destruct q; simpl.
  repeat rewrite concat_p1.
  reflexivity.
Defined.

Definition concat_A1_pp {A : Type} {f : A -> A} (p : forall x, f x = x)
  {x y : A} (q : x = y)
  {z : A} (s : y = z)
  :
  (ap f q) @ (p y @ s) = (p x) @ (q @ s).
Proof.
  destruct q, s; cbn.
  repeat rewrite concat_p1, concat_1p.
  reflexivity.
Defined.

Definition concat_pp_A1 {A : Type} {g : A -> A} (p : forall x, x = g x)
  {x y : A} (q : x = y)
  {w : A} (r : w = x)
  :
  (r @ p x) @ ap g q = (r @ q) @ p y.
Proof.
  destruct q; simpl.
  repeat rewrite concat_p1.
  reflexivity.
Defined.

Definition concat_p_A1p {A : Type} {g : A -> A} (p : forall x, x = g x)
  {x y : A} (q : x = y)
  {z : A} (s : g y = z)
  :
  p x @ (ap g q @ s) = q @ (p y @ s).
Proof.
  destruct q, s; simpl.
  repeat rewrite concat_p1, concat_1p.
  reflexivity.
Defined.
Definition apD10_1 {A} {B:A->Type} (f : forall x, B x) (x:A)
  : apD10 (idpath f) x = 1.
admit.
Defined.

Definition apD10_pp {A} {B:A->Type} {f f' f'' : forall x, B x}
  (h:f=f') (h':f'=f'') (x:A)
: apD10 (h @ h') x = apD10 h x @ apD10 h' x.
Proof.
  case h, h'; reflexivity.
Defined.

Definition apD10_V {A} {B:A->Type} {f g : forall x, B x} (h:f=g) (x:A)
  : apD10 (h^) x = (apD10 h x)^
:= match h with idpath => 1 end.
Definition ap10_1 {A B} {f:A->B} (x:A) : ap10 (idpath f) x = 1.
admit.
Defined.
Definition ap10_pp {A B} {f f' f'':A->B} (h:f=f') (h':f'=f'') (x:A)
  : ap10 (h @ h') x = ap10 h x @ ap10 h' x. exact (apD10_pp h h' x). Defined.
Definition ap10_V {A B} {f g : A->B} (h : f = g) (x:A)
  : ap10 (h^) x = (ap10 h x)^. exact (apD10_V h x). Defined.


Definition apD10_ap_precompose {A B C} (f : A -> B) {g g' : forall x:B, C x} (p : g = g') a
: apD10 (ap (fun h : forall x:B, C x => h oD f) p) a = apD10 p (f a).
Proof.
  destruct p; reflexivity.
Defined.
Definition ap10_ap_precompose {A B C} (f : A -> B) {g g' : B -> C} (p : g = g') a
: ap10 (ap (fun h : B -> C => h o f) p) a = ap10 p (f a). exact (apD10_ap_precompose f p a). Defined.

Definition apD10_ap_postcompose {A B C} (f : forall x, B x -> C) {g g' : forall x:A, B x} (p : g = g') a
: apD10 (ap (fun h : forall x:A, B x => fun x => f x (h x)) p) a = ap (f a) (apD10 p a).
Proof.
  destruct p; reflexivity.
Defined.
Definition ap10_ap_postcompose {A B C} (f : B -> C) {g g' : A -> B} (p : g = g') a
: ap10 (ap (fun h : A -> B => f o h) p) a = ap f (ap10 p a). exact (apD10_ap_postcompose (fun a => f) p a). Defined.
Definition transport_1 {A : Type} (P : A -> Type) {x : A} (u : P x)
  : 1 # u = u.
admit.
Defined.

Definition transport_pp {A : Type} (P : A -> Type) {x y z : A} (p : x = y) (q : y = z) (u : P x) :
  p @ q # u = q # p # u :=
  match q with idpath =>
    match p with idpath => 1 end
  end.
Definition transport_pV {A : Type} (P : A -> Type) {x y : A} (p : x = y) (z : P y)
  : p # p^ # z = z. exact ((transport_pp P p^ p z)^
  @ ap (fun r => transport P r z) (concat_Vp p)). Defined.
Definition transport_Vp {A : Type} (P : A -> Type) {x y : A} (p : x = y) (z : P x)
  : p^ # p # z = z. exact ((transport_pp P p p^ z)^
  @ ap (fun r => transport P r z) (concat_pV p)). Defined.


Definition transport_p_pp {A : Type} (P : A -> Type)
  {x y z w : A} (p : x = y) (q : y = z) (r : z = w)
  (u : P x)
  : ap (fun e => e # u) (concat_p_pp p q r)
    @ (transport_pp P (p@q) r u) @ ap (transport P r) (transport_pp P p q u)
  = (transport_pp P p (q@r) u) @ (transport_pp P q r (p#u))
  :> ((p @ (q @ r)) # u = r # q # p # u) .
Proof.
  destruct p, q, r.
 simpl.
 exact 1.
Defined.


Definition transport_pVp {A} (P : A -> Type) {x y:A} (p:x=y) (z:P x)
  : transport_pV P p (transport P p z)
  = ap (transport P p) (transport_Vp P p z).
Proof.
  destruct p; reflexivity.
Defined.



Definition transportD {A : Type} (B : A -> Type) (C : forall a:A, B a -> Type)
  {x1 x2 : A} (p : x1 = x2) (y : B x1) (z : C x1 y)
  : C x2 (p # y)
  :=
  match p with idpath => z end.

Definition transportD2 {A : Type} (B C : A -> Type) (D : forall a:A, B a -> C a -> Type)
  {x1 x2 : A} (p : x1 = x2) (y : B x1) (z : C x1) (w : D x1 y z)
  : D x2 (p # y) (p # z)
  :=
  match p with idpath => w end.
Definition ap011 {A B C} (f : A -> B -> C) {x x' y y'} (p : x = x') (q : y = y')
: f x y = f x' y'. exact (ap11 (ap f p) q). Defined.



Definition ap011D {A B C} (f : forall (a:A), B a -> C)
           {x x'} (p : x = x') {y y'} (q : p # y = y')
: f x y = f x' y'.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition ap01D1 {A B C} (f : forall (a:A), B a -> C a)
           {x x'} (p : x = x') {y y'} (q : p # y = y')
: transport C p (f x y) = f x' y'.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition apD011 {A B C} (f : forall (a:A) (b:B a), C a b)
           {x x'} (p : x = x') {y y'} (q : p # y = y')
: transport (C x') q (transportD B C p y (f x y)) = f x' y'.
Proof.
  destruct p, q; reflexivity.
Defined.
Definition transport2 {A : Type} (P : A -> Type) {x y : A} {p q : x = y}
  (r : p = q) (z : P x)
  : p # z = q # z. exact (ap (fun p' => p' # z) r). Defined.


Definition transport2_is_ap10 {A : Type} (Q : A -> Type) {x y : A} {p q : x = y}
  (r : p = q) (z : Q x)
  : transport2 Q r z = ap10 (ap (transport Q) r) z
  := match r with idpath => 1 end.

Definition transport2_p2p {A : Type} (P : A -> Type) {x y : A} {p1 p2 p3 : x = y}
  (r1 : p1 = p2) (r2 : p2 = p3) (z : P x)
  : transport2 P (r1 @ r2) z = transport2 P r1 z @ transport2 P r2 z.
Proof.
  destruct r1, r2; reflexivity.
Defined.

Definition transport2_V {A : Type} (Q : A -> Type) {x y : A} {p q : x = y}
  (r : p = q) (z : Q x)
  : transport2 Q (r^) z = (transport2 Q r z)^
  := match r with idpath => 1 end.

Definition concat_AT {A : Type} (P : A -> Type) {x y : A} {p q : x = y}
  {z w : P x} (r : p = q) (s : z = w)
  : ap (transport P p) s  @  transport2 P r w
    = transport2 P r z  @  ap (transport P q) s
  := match r with idpath => (concat_p1 _ @ (concat_1p _)^) end.


Lemma ap_transport {A} {P Q : A -> Type} {x y : A} (p : x = y) (f : forall x, P x -> Q x) (z : P x) :
  f y (p # z) = (p # (f x z)).
Proof.
  by induction p.
Defined.

Lemma ap_transportD {A : Type}
      (B : A -> Type) (C1 C2 : forall a : A, B a -> Type)
      (f : forall a b, C1 a b -> C2 a b)
      {x1 x2 : A} (p : x1 = x2) (y : B x1) (z : C1 x1 y)
: f x2 (p # y) (transportD B C1 p y z)
  = transportD B C2 p y (f x1 y z).
admit.
Defined.

Lemma ap_transportD2 {A : Type}
      (B C : A -> Type) (D1 D2 : forall a, B a -> C a -> Type)
      (f : forall a b c, D1 a b c -> D2 a b c)
      {x1 x2 : A} (p : x1 = x2) (y : B x1) (z : C x1) (w : D1 x1 y z)
: f x2 (p # y) (p # z) (transportD2 B C D1 p y z w)
  = transportD2 B C D2 p y z (f x1 y z w).
admit.
Defined.


Lemma ap_transport_pV {X} (Y : X -> Type) {x1 x2 : X} (p : x1 = x2)
      {y1 y2 : Y x2} (q : y1 = y2)
: ap (transport Y p) (ap (transport Y p^) q) =
  transport_pV Y p y1 @ q @ (transport_pV Y p y2)^.
admit.
Defined.


Definition transport_pV_ap {X} (P : X -> Type) (f : forall x, P x)
      {x1 x2 : X} (p : x1 = x2)
: ap (transport P p) (apD f p^) @ apD f p = transport_pV P p (f x2).
Proof.
  destruct p; reflexivity.
Defined.






Definition transport_const {A B : Type} {x1 x2 : A} (p : x1 = x2) (y : B)
  : transport (fun x => B) p y = y.
Proof.
  destruct p.
 exact 1.
Defined.

Definition transport2_const {A B : Type} {x1 x2 : A} {p q : x1 = x2}
  (r : p = q) (y : B)
  : transport_const p y = transport2 (fun _ => B) r y @ transport_const q y
  := match r with idpath => (concat_1p _)^ end.


Lemma transport_compose {A B} {x y : A} (P : B -> Type) (f : A -> B)
  (p : x = y) (z : P (f x))
  : transport (fun x => P (f x)) p z  =  transport P (ap f p) z.
Proof.
  destruct p; reflexivity.
Defined.

Lemma transport_precompose {A B C} (f : A -> B) (g g' : B -> C) (p : g = g')
: transport (fun h : B -> C => g o f = h o f) p 1 =
  ap (fun h => h o f) p.
admit.
Defined.


Definition transport_idmap_ap A (P : A -> Type) x y (p : x = y) (u : P x)
: transport P p u = transport idmap (ap P p) u
  := match p with idpath => idpath end.




Lemma apD_const {A B} {x y : A} (f : A -> B) (p: x = y) :
  apD f p = transport_const p (f x) @ ap f p.
admit.
Defined.
Definition concat2 {A} {x y z : A} {p p' : x = y} {q q' : y = z} (h : p = p') (h' : q = q')
  : p @ q = p' @ q'. exact (match h, h' with idpath, idpath => 1 end). Defined.

Notation "p @@ q" := (concat2 p q)%path (at level 20) : path_scope.
Definition inverse2 {A : Type} {x y : A} {p q : x = y} (h : p = q)
  : p^ = q^. exact (match h with idpath => 1 end). Defined.
Definition whiskerL {A : Type} {x y z : A} (p : x = y)
  {q r : y = z} (h : q = r) : p @ q = p @ r. exact (1 @@ h). Defined.
Definition whiskerR {A : Type} {x y z : A} {p q : x = y}
  (h : p = q) (r : y = z) : p @ r = q @ r. exact (h @@ 1). Defined.
Definition cancelL {A} {x y z : A} (p : x = y) (q r : y = z)
: (p @ q = p @ r) -> (q = r). exact (fun h => (concat_V_pp p q)^ @ whiskerL p^ h @ (concat_V_pp p r)). Defined.
Definition cancelR {A} {x y z : A} (p q : x = y) (r : y = z)
: (p @ r = q @ r) -> (p = q). exact (fun h => (concat_pp_V p r)^ @ whiskerR h r^ @ (concat_pp_V q r)). Defined.



Definition whiskerR_p1 {A : Type} {x y : A} {p q : x = y} (h : p = q) :
  (concat_p1 p) ^ @ whiskerR h 1 @ concat_p1 q = h
  :=
  match h with idpath =>
    match p with idpath =>
      1
    end end.
Definition whiskerR_1p {A : Type} {x y z : A} (p : x = y) (q : y = z) :
  whiskerR 1 q = 1 :> (p @ q = p @ q). exact (match q with idpath => 1 end). Defined.
Definition whiskerL_p1 {A : Type} {x y z : A} (p : x = y) (q : y = z) :
  whiskerL p 1 = 1 :> (p @ q = p @ q). exact (match q with idpath => 1 end). Defined.

Definition whiskerL_1p {A : Type} {x y : A} {p q : x = y} (h : p = q) :
  (concat_1p p) ^ @ whiskerL 1 h @ concat_1p q = h
  :=
  match h with idpath =>
    match p with idpath =>
      1
    end end.
Definition concat2_p1 {A : Type} {x y : A} {p q : x = y} (h : p = q) :
  h @@ 1 = whiskerR h 1 :> (p @ 1 = q @ 1). exact (match h with idpath => 1 end). Defined.
Definition concat2_1p {A : Type} {x y : A} {p q : x = y} (h : p = q) :
  1 @@ h = whiskerL 1 h :> (1 @ p = 1 @ q). exact (match h with idpath => 1 end). Defined.




Definition whiskerL_pp {A} {x y z : A} (p : x = y) {q q' q'' : y = z}
           (r : q = q') (s : q' = q'')
: whiskerL p (r @ s) = whiskerL p r @ whiskerL p s.
Proof.
  destruct p, r, s; reflexivity.
Defined.

Definition whiskerR_pp {A} {x y z : A} {p p' p'' : x = y} (q : y = z)
           (r : p = p') (s : p' = p'')
: whiskerR (r @ s) q = whiskerR r q @ whiskerR s q.
Proof.
  destruct q, r, s; reflexivity.
Defined.


Definition whiskerL_VpL {A} {x y z : A} (p : x = y)
           {q q' : y = z} (r : q = q')
: (concat_V_pp p q)^ @ whiskerL p^ (whiskerL p r) @ concat_V_pp p q'
  = r.
Proof.
  destruct p, r, q.
reflexivity.
Defined.

Definition whiskerL_pVL {A} {x y z : A} (p : y = x)
           {q q' : y = z} (r : q = q')
: (concat_p_Vp p q)^ @ whiskerL p (whiskerL p^ r) @ concat_p_Vp p q'
  = r.
Proof.
  destruct p, r, q.
reflexivity.
Defined.

Definition whiskerR_pVR {A} {x y z : A} {p p' : x = y}
           (r : p = p') (q : y = z)
: (concat_pp_V p q)^ @ whiskerR (whiskerR r q) q^ @ concat_pp_V p' q
  = r.
Proof.
  destruct p, r, q.
reflexivity.
Defined.

Definition whiskerR_VpR {A} {x y z : A} {p p' : x = y}
           (r : p = p') (q : z = y)
: (concat_pV_p p q)^ @ whiskerR (whiskerR r q^) q @ concat_pV_p p' q
  = r.
Proof.
  destruct p, r, q.
reflexivity.
Defined.


Definition concat_concat2 {A : Type} {x y z : A} {p p' p'' : x = y} {q q' q'' : y = z}
  (a : p = p') (b : p' = p'') (c : q = q') (d : q' = q'') :
  (a @@ c) @ (b @@ d) = (a @ b) @@ (c @ d).
Proof.
  case d.
  case c.
  case b.
  case a.
  reflexivity.
Defined.


Definition concat_whisker {A} {x y z : A} (p p' : x = y) (q q' : y = z) (a : p = p') (b : q = q') :
  (whiskerR a q) @ (whiskerL p' b) = (whiskerL p b) @ (whiskerR a q')
  :=
  match b with
    idpath =>
    match a with idpath =>
      (concat_1p _)^
    end
  end.




Definition pentagon {A : Type} {v w x y z : A} (p : v = w) (q : w = x) (r : x = y) (s : y = z)
  : whiskerL p (concat_p_pp q r s)
      @ concat_p_pp p (q@r) s
      @ whiskerR (concat_p_pp p q r) s
  = concat_p_pp p q (r@s) @ concat_p_pp (p@q) r s.
Proof.
  case p, q, r, s.
 reflexivity.
Defined.


Definition triangulator {A : Type} {x y z : A} (p : x = y) (q : y = z)
  : concat_p_pp p 1 q @ whiskerR (concat_p1 p) q
  = whiskerL p (concat_1p q).
Proof.
  case p, q.
 reflexivity.
Defined.
Definition eckmann_hilton {A : Type} {x:A} (p q : 1 = 1 :> (x = x)) : p @ q = q @ p. exact ((whiskerR_p1 p @@ whiskerL_1p q)^
  @ (concat_p1 _ @@ concat_p1 _)
  @ (concat_1p _ @@ concat_1p _)
  @ (concat_whisker _ _ _ _ p q)
  @ (concat_1p _ @@ concat_1p _)^
  @ (concat_p1 _ @@ concat_p1 _)^
  @ (whiskerL_1p q @@ whiskerR_p1 p)). Defined.
Definition ap02 {A B : Type} (f:A->B) {x y:A} {p q:x=y} (r:p=q) : ap f p = ap f q. exact (match r with idpath => 1 end). Defined.

Definition ap02_pp {A B} (f:A->B) {x y:A} {p p' p'':x=y} (r:p=p') (r':p'=p'')
  : ap02 f (r @ r') = ap02 f r @ ap02 f r'.
Proof.
  case r, r'; reflexivity.
Defined.

Definition ap02_p2p {A B} (f:A->B) {x y z:A} {p p':x=y} {q q':y=z} (r:p=p') (s:q=q')
  : ap02 f (r @@ s) =   ap_pp f p q
                      @ (ap02 f r  @@  ap02 f s)
                      @ (ap_pp f p' q')^.
Proof.
  case r, s, p, q.
reflexivity.
Defined.

Definition apD02 {A : Type} {B : A -> Type} {x y : A} {p q : x = y}
  (f : forall x, B x) (r : p = q)
  : apD f p = transport2 B r (f x) @ apD f q
  := match r with idpath => (concat_1p _)^ end.


Definition apD02_pp {A} (B : A -> Type) (f : forall x:A, B x) {x y : A}
  {p1 p2 p3 : x = y} (r1 : p1 = p2) (r2 : p2 = p3)
  : apD02 f (r1 @ r2)
  = apD02 f r1
  @ whiskerL (transport2 B r1 (f x)) (apD02 f r2)
  @ concat_p_pp _ _ _
  @ (whiskerR (transport2_p2p B r1 r2 (f x))^ (apD f p3)).
Proof.
  destruct r1, r2.
destruct p1.
reflexivity.
Defined.


Definition ap_transport_Vp {A B} (p q : A = B) (r : q = p) (z : A)
: ap (transport idmap q^) (ap (fun s => transport idmap s z) r)
  @ ap (fun s => transport idmap s (p # z)) (inverse2 r)
  @ transport_Vp idmap p z
  = transport_Vp idmap q z.
Proof.
  by path_induction.
Defined.

Hint Resolve
  concat_1p concat_p1 concat_p_pp
  inv_pp inv_V
 : path_hints.


Hint Rewrite
@concat_p1
@concat_1p
@concat_p_pp
@concat_pV
@concat_Vp
@concat_V_pp
@concat_p_Vp
@concat_pp_V
@concat_pV_p

@inv_V
@moveR_Mp
@moveR_pM
@moveL_Mp
@moveL_pM
@moveL_1M
@moveL_M1
@moveR_M1
@moveR_1M
@ap_1

@inverse_ap
@ap_idmap

@ap_const

@apD10_1
:paths.
Module Export Contractible.
Import HoTT_DOT_Basics_DOT_Overture.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.Basics.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.Basics.Overture.




Generalizable Variables A B f.
Definition path_contr `{Contr A} (x y : A) : x = y. exact ((contr x)^ @ (contr y)). Defined.


Definition path2_contr `{Contr A} {x y : A} (p q : x = y) : p = q.
Proof.
  assert (K : forall (r : x = y), r = path_contr x y).
    intro r; destruct r; symmetry; now apply concat_Vp.
  transitivity (path_contr x y);auto with path_hints.
Defined.
Global Instance contr_paths_contr `{Contr A} (x y : A) : Contr (x = y) | 10000. exact (let c := {|
  center := (contr x)^ @ contr y;
  contr := path2_contr ((contr x)^ @ contr y)
|} in c). Defined.


Global Instance contr_basedpaths {X : Type} (x : X) : Contr {y : X & x = y} | 100.
  exists (x ; 1).
  intros [y []]; reflexivity.
Defined.

Global Instance contr_basedpaths' {X : Type} (x : X) : Contr {y : X & y = x} | 100.
  exists (existT (fun y => y = x) x 1).
  intros [y []]; reflexivity.
Defined.

End Contractible.
Module Export Equivalences.
Local Open Scope equiv_scope.





Generalizable Variables A B C f g.


Global Instance isequiv_idmap (A : Type) : IsEquiv idmap | 0 :=
  BuildIsEquiv A A idmap idmap (fun _ => 1) (fun _ => 1) (fun _ => 1).
Definition equiv_idmap (A : Type) : A <~> A. exact (BuildEquiv A A idmap _). Defined.
Global Instance isequiv_compose `{IsEquiv A B f} `{IsEquiv B C g}
  : IsEquiv (compose g f) | 1000. exact (BuildIsEquiv A C (compose g f)
    (compose f^-1 g^-1)
    (fun c => ap g (eisretr f (g^-1 c)) @ eisretr g c)
    (fun a => ap (f^-1) (eissect g (f a)) @ eissect f a)
    (fun a =>
      (whiskerL _ (eisadj g (f a))) @
      (ap_pp g _ _)^ @
      ap02 g
      ( (concat_A1p (eisretr f) (eissect g (f a)))^ @
        (ap_compose f^-1 f _ @@ eisadj f a) @
        (ap_pp f _ _)^
      ) @
      (ap_compose f g _)^
    )). Defined.
Definition isequiv_compose'
  {A B : Type} (f : A -> B) (_ : IsEquiv f)
  {C : Type} (g : B -> C) (_ : IsEquiv g)
  : IsEquiv (g o f). exact (isequiv_compose). Defined.
Definition equiv_compose {A B C : Type} (g : B -> C) (f : A -> B)
  `{IsEquiv B C g} `{IsEquiv A B f}
  : A <~> C. exact (BuildEquiv A C (compose g f) _). Defined.
Definition equiv_compose' {A B C : Type} (g : B <~> C) (f : A <~> B)
  : A <~> C. exact (equiv_compose g f). Defined.


Section IsEquivHomotopic.

  Context {A B : Type} (f : A -> B) {g : A -> B}.
  Context `{IsEquiv A B f}.
  Hypothesis h : f == g.

  Let sect := (fun b:B => (h (f^-1 b))^ @ eisretr f b).
  Let retr := (fun a:A => (ap f^-1 (h a))^ @ eissect f a).


  Let adj (a : A) : sect (g a) = ap g (retr a).
admit.
Defined.
Definition isequiv_homotopic : IsEquiv g. exact (BuildIsEquiv _ _ g (f ^-1) sect retr adj). Defined.

End IsEquivHomotopic.


Section EquivInverse.

  Context {A B : Type} (f : A -> B) {feq : IsEquiv f}.

  Theorem other_adj (b : B) : eissect f (f^-1 b) = ap f^-1 (eisretr f b).
admit.
Defined.
Global Instance isequiv_inverse : IsEquiv f^-1 | 10000. exact (BuildIsEquiv B A f^-1 f (eissect f) (eisretr f) other_adj). Defined.
End EquivInverse.


Theorem equiv_inverse {A B : Type} : (A <~> B) -> (B <~> A).
Proof.
  intro e.
  exists (e^-1).
  apply isequiv_inverse.
Defined.
Global Instance symmetric_equiv : Symmetric Equiv | 0.
admit.
Defined.
Definition cancelR_isequiv {A B C} (f : A -> B) {g : B -> C}
  `{IsEquiv A B f} `{IsEquiv A C (g o f)}
  : IsEquiv g. exact (isequiv_homotopic (compose (compose g f) f^-1)
       (fun b => ap g (eisretr f b))). Defined.
Definition cancelR_equiv {A B C} (f : A -> B) {g : B -> C}
  `{IsEquiv A B f} `{IsEquiv A C (g o f)}
  : B <~> C. exact (BuildEquiv B C g (cancelR_isequiv f)). Defined.
Definition cancelL_isequiv {A B C} (g : B -> C) {f : A -> B}
  `{IsEquiv B C g} `{IsEquiv A C (g o f)}
  : IsEquiv f. exact (isequiv_homotopic (compose g^-1 (compose g f))
       (fun a => eissect g (f a))). Defined.
Definition cancelL_equiv {A B C} (g : B -> C) {f : A -> B}
  `{IsEquiv B C g} `{IsEquiv A C (g o f)}
  : A <~> B. exact (BuildEquiv _ _ f (cancelL_isequiv g)). Defined.


Definition isequiv_commsq {A B C D}
           (f : A -> B) (g : C -> D) (h : A -> C) (k : B -> D)
           (p : k o f == g o h)
           `{IsEquiv _ _ f} `{IsEquiv _ _ h} `{IsEquiv _ _ k}
: IsEquiv g.
Proof.
  refine (@cancelR_isequiv _ _ _ h g _ _).
  refine (isequiv_homotopic _ p).
Defined.

Definition isequiv_commsq' {A B C D}
           (f : A -> B) (g : C -> D) (h : A -> C) (k : B -> D)
           (p : g o h == k o f)
           `{IsEquiv _ _ g} `{IsEquiv _ _ h} `{IsEquiv _ _ k}
: IsEquiv f.
Proof.
  refine (@cancelL_isequiv _ _ _ k f _ _).
  refine (isequiv_homotopic _ p).
Defined.


Section EquivTransport.

  Context {A : Type} (P : A -> Type) (x y : A) (p : x = y).
Global Instance isequiv_transport : IsEquiv (transport P p) | 0. exact (BuildIsEquiv (P x) (P y) (transport P p) (transport P p^)
    (transport_pV P p) (transport_Vp P p) (transport_pVp P p)). Defined.

End EquivTransport.



Section Adjointify.

  Context {A B : Type} (f : A -> B) (g : B -> A).
  Context (isretr : Sect g f) (issect : Sect f g).


  Let issect' := fun x =>
    ap g (ap f (issect x)^)  @  ap g (isretr (f x))  @  issect x.

  Let is_adjoint' (a : A) : isretr (f a) = ap f (issect' a).
admit.
Defined.
Definition isequiv_adjointify : IsEquiv f. exact (BuildIsEquiv A B f g isretr issect' is_adjoint'). Defined.
Definition equiv_adjointify : A <~> B. exact (BuildEquiv A B f isequiv_adjointify). Defined.

End Adjointify.
Definition moveR_equiv_M `{IsEquiv A B f} (x : A) (y : B) (p : x = f^-1 y)
  : (f x = y). exact (ap f p @ eisretr f y). Defined.
Definition moveL_equiv_M `{IsEquiv A B f} (x : A) (y : B) (p : f^-1 y = x)
  : (y = f x). exact ((eisretr f y)^ @ ap f p). Defined.
Definition moveR_equiv_V `{IsEquiv A B f} (x : B) (y : A) (p : x = f y)
  : (f^-1 x = y). exact (ap (f^-1) p @ eissect f y). Defined.
Definition moveL_equiv_V `{IsEquiv A B f} (x : B) (y : A) (p : f y = x)
  : (y = f^-1 x). exact ((eissect f y)^ @ ap (f^-1) p). Defined.


Lemma contr_equiv A {B} (f : A -> B) `{IsEquiv A B f} `{Contr A}
  : Contr B.
admit.
Defined.
Definition contr_equiv' A {B} `(f : A <~> B) `{Contr A}
  : Contr B. exact (contr_equiv A f). Defined.



Lemma equiv_contr_contr {A B : Type} `{Contr A} `{Contr B}
  : (A <~> B).
Proof.
  apply equiv_adjointify with (fun _ => center B) (fun _ => center A);
  intros ?; apply contr.
Defined.
Global Instance isequiv_precompose `{Funext} {A B C : Type}
  (f : A -> B) `{IsEquiv A B f}
  : IsEquiv (fun g => @compose A B C g f) | 1000. exact (isequiv_adjointify (fun g => @compose A B C g f)
    (fun h => @compose B A C h f^-1)
    (fun h => path_forall _ _ (fun x => ap h (eissect f x)))
    (fun g => path_forall _ _ (fun y => ap g (eisretr f y)))). Defined.
Definition equiv_precompose `{Funext} {A B C : Type}
  (f : A -> B) `{IsEquiv A B f}
  : (B -> C) <~> (A -> C). exact (BuildEquiv _ _ (fun g => @compose A B C g f) _). Defined.
Definition equiv_precompose' `{Funext} {A B C : Type} (f : A <~> B)
  : (B -> C) <~> (A -> C). exact (BuildEquiv _ _ (fun g => @compose A B C g f) _). Defined.
Global Instance isequiv_postcompose `{Funext} {A B C : Type}
  (f : B -> C) `{IsEquiv B C f}
  : IsEquiv (fun g => @compose A B C f g) | 1000. exact (isequiv_adjointify (fun g => @compose A B C f g)
    (fun h => @compose A C B f^-1 h)
    (fun h => path_forall _ _ (fun x => eisretr f (h x)))
    (fun g => path_forall _ _ (fun y => eissect f (g y)))). Defined.
Definition equiv_postcompose `{Funext} {A B C : Type}
  (f : B -> C) `{IsEquiv B C f}
  : (A -> B) <~> (A -> C). exact (BuildEquiv _ _ (fun g => @compose A B C f g) _). Defined.
Definition equiv_postcompose' `{Funext} {A B C : Type} (f : B <~> C)
  : (A -> B) <~> (A -> C). exact (BuildEquiv _ _ (fun g => @compose A B C f g) _). Defined.



Definition isequiv_isequiv_precompose {A B : Type} (f : A -> B)
  (precomp := (fun (C : Type) (h : B -> C) => h o f))
  (Aeq : IsEquiv (precomp A)) (Beq : IsEquiv (precomp B))
  : IsEquiv f.
admit.
Defined.
Global Instance isequiv_ap `{IsEquiv A B f} (x y : A)
  : IsEquiv (@ap A B f x y) | 1000. exact (isequiv_adjointify (ap f)
  (fun q => (eissect f x)^  @  ap f^-1 q  @  eissect f y)
  (fun q =>
    ap_pp f _ _
    @ whiskerR (ap_pp f _ _) _
    @ ((ap_V f _ @ inverse2 (eisadj f _)^)
      @@ (ap_compose f^-1 f _)^
      @@ (eisadj f _)^)
    @ concat_pA1_p (eisretr f) _ _
    @ whiskerR (concat_Vp _) _
    @ concat_1p _)
  (fun p =>
    whiskerR (whiskerL _ (ap_compose f f^-1 _)^) _
    @ concat_pA1_p (eissect f) _ _
    @ whiskerR (concat_Vp _) _
    @ concat_1p _)). Defined.
Definition equiv_ind `{IsEquiv A B f} (P : B -> Type)
  : (forall x:A, P (f x)) -> forall y:B, P y. exact (fun g y => transport P (eisretr f y) (g (f^-1 y))). Defined.

Arguments equiv_ind {A B} f {_} P _ _.

Definition equiv_ind_comp `{IsEquiv A B f} (P : B -> Type)
  (df : forall x:A, P (f x)) (x : A)
  : equiv_ind f P df (f x) = df x.
Proof.
  unfold equiv_ind.
  rewrite eisadj.
  rewrite <- transport_compose.
  exact (apD df (eissect f x)).
Defined.



Ltac equiv_intro E x :=
  match goal with
    | |- forall y, @?Q y =>
      refine (equiv_ind E Q _); intros x
  end.


Definition equiv_composeR' {A B C} (f : A <~> B) (g : B <~> C)
  := equiv_compose' g f.

End Equivalences.






Definition Lift (A : Type@{i}) : Type@{j}
  := Eval hnf in let enforce_lt := Type@{i} : Type@{j} in A.
Definition lift {A} : A -> Lift A. exact (fun x => x). Defined.
Definition lower {A} : Lift A -> A. exact (fun x => x). Defined.
Global Instance isequiv_lift T : IsEquiv (@lift T). exact (@BuildIsEquiv
       _ _
       (@lift T)
       (@lower T)
       (fun _ => idpath)
       (fun _ => idpath)
       (fun _ => idpath)). Defined.
Definition Lift' (A : Type@{i}) : Type@{j}. exact (A). Defined.
Definition lift' {A : Type@{i}} : A -> Lift'@{i j} A. exact (fun x => x). Defined.
Definition lower' {A : Type@{i}} : Lift'@{i j} A -> A. exact (fun x => x). Defined.
Global Instance isequiv_lift' T : IsEquiv (@lift'@{i j} T). exact (@BuildIsEquiv
       _ _
       (@lift' T)
       (@lower' T)
       (fun _ => idpath)
       (fun _ => idpath)
       (fun _ => idpath)). Defined.
Import HoTT_DOT_Basics_DOT_Overture.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.Basics.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.Basics.Overture.





Definition NaiveFunext :=
  forall (A : Type) (P : A -> Type) (f g : forall x, P x),
    (forall x, f x = g x) -> (f = g).



Definition WeakFunext :=
  forall (A : Type) (P : A -> Type),
    (forall x, Contr (P x)) -> Contr (forall x, P x).


Definition Funext_type :=
  forall (A : Type) (P : A -> Type) f g, IsEquiv (@apD10 A P f g).



Definition Funext_implies_NaiveFunext : Funext_type -> NaiveFunext.
Proof.
  intros fe A P f g h.
  unfold Funext_type in *.
  exact ((@apD10 A P f g)^-1 h)%equiv.
Defined.

Definition NaiveFunext_implies_WeakFunext : NaiveFunext -> WeakFunext.
Proof.
  intros nf A P Pc.
  exists (fun x => center (P x)).
  intros f; apply nf; intros x.
  apply contr.
Defined.



Section Homotopies.

  Context (wf : WeakFunext).
  Context {A:Type} {B : A -> Type}.

  Context (f : forall x, B x).
Let idhtpy : f == f. exact (fun x => idpath (f x)). Defined.



  Global Instance contr_basedhtpy : Contr {g : forall x, B x & f == g } | 1.
  Proof.
    exists (f;idhtpy).
intros [g h].

    pose (r := fun k => existT (fun g => f == g)
      (fun x => (k x).1) (fun x => (k x).2)).
    pose (s := fun (g : forall x, B x) (h : f == g) x => (g x ; h x)).

    change (r (fun x => (f x ; idpath (f x))) = r (s g h)).
    apply ap; refine (@path_contr _ _ _ _).
    apply wf.
intros x; exact (contr_basedpaths (f x)).
  Defined.



  Context (Q : forall g (h : f == g), Type).
  Context (d : Q f idhtpy).
Definition htpy_ind g h : Q g h. exact (@transport _ (fun gh => Q gh.1 gh.2) (f;idhtpy) (g;h)
         (@path_contr _ _ _ _) d). Defined.
Definition htpy_ind_beta : htpy_ind f idhtpy = d. exact (transport (fun p : (f;idhtpy) = (f;idhtpy) =>
                    transport (fun gh => Q gh.1 gh.2) p d = d)
         (@path2_contr _ _ _ _
           (path_contr (f;idhtpy) (f;idhtpy)) (idpath _))^
         (idpath _)). Defined.

End Homotopies.


Theorem WeakFunext_implies_Funext : WeakFunext -> Funext_type.
Proof.
  intros wf; hnf; intros A B f g.
  refine (isequiv_adjointify (@apD10 A B f g)
    (htpy_ind wf f (fun g' _ => f = g') idpath g) _ _).
  revert g; refine (htpy_ind wf _ _ _).
    refine (ap _ (htpy_ind_beta wf _ _ _)).
  intros h; destruct h.
    refine (htpy_ind_beta wf _ _ _).
Defined.
Definition NaiveFunext_implies_Funext : NaiveFunext -> Funext_type. exact (WeakFunext_implies_Funext o NaiveFunext_implies_WeakFunext). Defined.



Lemma Funext_downward_closed `{H : Funext_type} : Funext_type.
admit.
Defined.
Module Export Pointed.
Import HoTT_DOT_Basics_DOT_Overture.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.Basics.

Import HoTT_DOT_Basics_DOT_Overture.HoTT.Basics.Overture.


Generalizable Variables A B f.
Global Instance ispointed_contr `{Contr A} : IsPointed A. exact (center A). Defined.
Global Instance ispointed_forall `{H : forall a : A, IsPointed (B a)}
: IsPointed (forall a, B a).
admit.
Defined.
Global Instance ispointed_sigma `{IsPointed A} `{IsPointed (B (point A))}
: IsPointed (sigT B). exact ((point A; point (B (point A)))). Defined.
Global Instance ispointed_prod `{IsPointed A, IsPointed B} : IsPointed (A * B). exact ((point A, point B)). Defined.
Global Instance ispointed_loop_space A (a : A) : IsPointed (a = a).
admit.
Defined.
Definition loopSpace (A : pointedType) : pointedType. exact ((A.1 = A.1; idpath)). Defined.

Fixpoint iteratedLoopSpace (n : nat) (A : Type) `{H : IsPointed A} {struct n} : pointedType
  := match n with
       | O => existT IsPointed A (@point A H)
       | S p => iteratedLoopSpace p (point = point)
     end.

End Pointed.

Module Export HoTT_DOT_Basics_DOT_Trunc.
Module Export HoTT.
Module Export Basics.
Module Export Trunc.
Import HoTT_DOT_Basics_DOT_Overture.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.Basics.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.Basics.Overture.
Local Open Scope equiv_scope.
Local Open Scope trunc_scope.
Generalizable Variables A B m n f.
Fixpoint trunc_index_leq (m n : trunc_index) : Type. exact (match m, n with
       | -2, _ => Unit
       | m'.+1, -2 => Empty
       | m'.+1, n'.+1 => trunc_index_leq m' n'
     end). Defined.

Notation "m <= n" := (trunc_index_leq m n) (at level 70, no associativity) : trunc_scope.
Definition contr_trunc_minus_two `{H : IsTrunc -2 A} : Contr A. exact (H). Defined.


Global Instance trunc_succ `{IsTrunc n A} : IsTrunc n.+1 A | 1000.
admit.
Defined.

Global Instance trunc_leq {m n} (Hmn : m <= n) `{IsTrunc m A} : IsTrunc n A | 1000.
admit.
Defined.
Definition trunc_contr {n} {A} `{Contr A} : IsTrunc n A. exact ((@trunc_leq -2 n tt _ _)). Defined.
Definition trunc_hprop {n} {A} `{IsHProp A} : IsTrunc n.+1 A. exact ((@trunc_leq -1 n.+1 tt _ _)). Defined.
Definition trunc_hset {n} {A} `{IsHSet A} : IsTrunc n.+1.+1 A. exact ((@trunc_leq 0 n.+1.+1 tt _ _)). Defined.


Hint Immediate trunc_contr : typeclass_instances.
Hint Immediate trunc_hprop : typeclass_instances.
Hint Immediate trunc_hset : typeclass_instances.


Definition trunc_equiv A {B} (f : A -> B)
  `{IsTrunc n A} `{IsEquiv A B f}
  : IsTrunc n B.
admit.
Defined.
Definition trunc_equiv' A {B} (f : A <~> B) `{IsTrunc n A}
  : IsTrunc n B. exact (trunc_equiv A f). Defined.



Class IsTruncMap (n : trunc_index) {X Y : Type} (f : X -> Y) :=
  istruncmap_fiber : forall y:Y, IsTrunc n (hfiber f y).

Global Existing Instance istruncmap_fiber.





Record TruncType (n : trunc_index) := BuildTruncType {
  trunctype_type : Type ;
  istrunc_trunctype_type : IsTrunc n trunctype_type
}.

Coercion trunctype_type : TruncType >-> Sortclass.
Global Existing Instance istrunc_trunctype_type.


Canonical Structure default_TruncType := fun n T P => (@BuildTruncType n T P).




Lemma contr_inhabited_hprop (A : Type) `{H : IsHProp A} (x : A)
  : Contr A.
admit.
Defined.


Global Instance hprop_inhabited_contr (A : Type) : (A -> Contr A) -> IsHProp A | 10000.
admit.
Defined.


Theorem path_ishprop `{H : IsHProp A} : forall x y : A, x = y.
admit.
Defined.


Theorem hprop_allpath (A : Type) : (forall (x y : A), x = y) -> IsHProp A.
  intros H x y.
  pose (C := BuildContr A x (H x)).
  apply contr_paths_contr.
Defined.


Definition isequiv_iff_hprop `{IsHProp A} `{IsHProp B}
  (f : A -> B) (g : B -> A)
: IsEquiv f.
Proof.
  apply (isequiv_adjointify f g);
    intros ?; apply path_ishprop.
Defined.

Definition equiv_iff_hprop_uncurried `{IsHProp A} `{IsHProp B}
  : (A <-> B) -> (A <~> B).
Proof.
  intros [f g].
  apply (equiv_adjointify f g);
    intros ?; apply path_ishprop.
Defined.
Definition equiv_iff_hprop `{IsHProp A} `{IsHProp B}
  : (A -> B) -> (B -> A) -> (A <~> B). exact (fun f g => equiv_iff_hprop_uncurried (f, g)). Defined.



Class WeaklyConstant {A B} (f : A -> B) :=
  wconst : forall x y, f x = f y.

Class Collapsible (A : Type) :=
  { collapse : A -> A ;
    wconst_collapse : WeaklyConstant collapse
  }.
Global Existing Instance wconst_collapse.

Class PathCollapsible (A : Type) :=
  path_coll : forall (x y : A), Collapsible (x = y).
Global Existing Instance path_coll.

Global Instance collapsible_decidable (A : Type) `{Decidable A}
: Collapsible A.
Proof.
  destruct (dec A) as [a | na].
  -
 exists (const a).
    intros x y; reflexivity.
  -
 exists idmap.
    intros x y; destruct (na x).
Defined.

Global Instance pathcoll_decpaths (A : Type) `{DecidablePaths A}
: PathCollapsible A.
Proof.
  intros x y; exact _.
Defined.

Global Instance hset_pathcoll (A : Type) `{PathCollapsible A}
: IsHSet A.
Proof.
  intros x y.
  assert (h : forall p:x=y, p = (collapse (idpath x))^ @ collapse p).
  {
 intros []; symmetry; by apply concat_Vp.
}
  apply hprop_allpath; intros p q.
  refine (h p @ _ @ (h q)^).
  apply whiskerL.
  apply wconst.
Defined.

Definition collapsible_hprop (A : Type) `{IsHProp A}
: Collapsible A.
Proof.
  exists idmap.
  intros x y; apply path_ishprop.
Defined.

Definition pathcoll_hset (A : Type) `{IsHSet A}
: PathCollapsible A.
Proof.
  intros x y; apply collapsible_hprop; exact _.
Defined.

Corollary hset_decpaths (A : Type) `{DecidablePaths A}
: IsHSet A.
admit.
Defined.

End Trunc.

End Basics.

End HoTT.

End HoTT_DOT_Basics_DOT_Trunc.

Module Export HoTT_DOT_Basics.
Module Export HoTT.
Module Export Basics.
Import HoTT_DOT_Basics_DOT_Overture.
Import HoTT_DOT_Basics_DOT_Trunc.
Import HoTT_DOT_Basics_DOT_Trunc.HoTT.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.
Import HoTT_DOT_Basics_DOT_Trunc.HoTT.Basics.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.Basics.
Export HoTT_DOT_Basics_DOT_Overture.HoTT.Basics.Overture.
Export HoTT_DOT_Basics_DOT_Trunc.HoTT.Basics.Trunc.

End Basics.

End HoTT.

End HoTT_DOT_Basics.
Module Export Paths.
Import HoTT_DOT_Basics_DOT_Overture.
Import HoTT_DOT_Basics_DOT_Trunc.
Import HoTT_DOT_Basics.
Import HoTT_DOT_Basics_DOT_Trunc.HoTT.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.
Import HoTT_DOT_Basics.HoTT.
Import HoTT_DOT_Basics_DOT_Trunc.HoTT.Basics.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.Basics.

Import HoTT_DOT_Basics.HoTT.Basics.
Local Open Scope equiv_scope.

Generalizable Variables A B f x y z.







Definition transport_paths_l {A : Type} {x1 x2 y : A} (p : x1 = x2) (q : x1 = y)
  : transport (fun x => x = y) p q = p^ @ q.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition transport_paths_r {A : Type} {x y1 y2 : A} (p : y1 = y2) (q : x = y1)
  : transport (fun y => x = y) p q = q @ p.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition transport_paths_lr {A : Type} {x1 x2 : A} (p : x1 = x2) (q : x1 = x1)
  : transport (fun x => x = x) p q = p^ @ q @ p.
Proof.
  destruct p; simpl.
  exact ((concat_1p q)^ @ (concat_p1 (1 @ q))^).
Defined.

Definition transport_paths_Fl {A B : Type} {f : A -> B} {x1 x2 : A} {y : B}
  (p : x1 = x2) (q : f x1 = y)
  : transport (fun x => f x = y) p q = (ap f p)^ @ q.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition transport_paths_Fr {A B : Type} {g : A -> B} {y1 y2 : A} {x : B}
  (p : y1 = y2) (q : x = g y1)
  : transport (fun y => x = g y) p q = q @ (ap g p).
Proof.
  destruct p.
symmetry; apply concat_p1.
Defined.

Definition transport_paths_FlFr {A B : Type} {f g : A -> B} {x1 x2 : A}
  (p : x1 = x2) (q : f x1 = g x1)
  : transport (fun x => f x = g x) p q = (ap f p)^ @ q @ (ap g p).
Proof.
  destruct p; simpl.
  exact ((concat_1p q)^ @ (concat_p1 (1 @ q))^).
Defined.

Definition transport_paths_FlFr_D {A : Type} {B : A -> Type}
  {f g : forall a, B a} {x1 x2 : A} (p : x1 = x2) (q : f x1 = g x1)
: transport (fun x => f x = g x) p q
  = (apD f p)^ @ ap (transport B p) q @ (apD g p).
Proof.
  destruct p; simpl.
  exact ((ap_idmap _)^ @ (concat_1p _)^ @ (concat_p1 _)^).
Defined.

Definition transport_paths_FFlr {A B : Type} {f : A -> B} {g : B -> A} {x1 x2 : A}
  (p : x1 = x2) (q : g (f x1) = x1)
  : transport (fun x => g (f x) = x) p q = (ap g (ap f p))^ @ q @ p.
Proof.
  destruct p; simpl.
  exact ((concat_1p q)^ @ (concat_p1 (1 @ q))^).
Defined.

Definition transport_paths_lFFr {A B : Type} {f : A -> B} {g : B -> A} {x1 x2 : A}
  (p : x1 = x2) (q : x1 = g (f x1))
  : transport (fun x => x = g (f x)) p q = p^ @ q @ (ap g (ap f p)).
Proof.
  destruct p; simpl.
  exact ((concat_1p q)^ @ (concat_p1 (1 @ q))^).
Defined.
Definition equiv_ap `(f : A -> B) `{IsEquiv A B f} (x y : A)
  : (x = y) <~> (f x = f y). exact (BuildEquiv _ _ (ap f) _). Defined.
Definition equiv_inj `(f : A -> B) `{IsEquiv A B f} {x y : A}
  : (f x = f y) -> (x = y). exact ((ap f)^-1). Defined.



Global Instance isequiv_path_inverse {A : Type} (x y : A)
  : IsEquiv (@inverse A x y) | 0
  := BuildIsEquiv _ _ _ (@inverse A y x) (@inv_V A y x) (@inv_V A x y) _.
Proof.
  intros p; destruct p; reflexivity.
Defined.
Definition equiv_path_inverse {A : Type} (x y : A)
  : (x = y) <~> (y = x). exact (BuildEquiv _ _ (@inverse A x y) _). Defined.

Global Instance isequiv_concat_l {A : Type} `(p : x = y:>A) (z : A)
  : IsEquiv (@transitivity A _ _ x y z p) | 0
  := BuildIsEquiv _ _ _ (concat p^)
     (concat_p_Vp p) (concat_V_pp p) _.
Proof.
  intros q; destruct p; destruct q; reflexivity.
Defined.
Definition equiv_concat_l {A : Type} `(p : x = y) (z : A)
  : (y = z) <~> (x = z). exact (BuildEquiv _ _ (concat p) _). Defined.

Global Instance isequiv_concat_r {A : Type} `(p : y = z) (x : A)
  : IsEquiv (fun q:x=y => q @ p) | 0
  := BuildIsEquiv _ _ (fun q => q @ p) (fun q => q @ p^)
     (fun q => concat_pV_p q p) (fun q => concat_pp_V q p) _.
Proof.
  intros q; destruct p; destruct q; reflexivity.
Defined.
Definition equiv_concat_r {A : Type} `(p : y = z) (x : A)
  : (x = y) <~> (x = z). exact (BuildEquiv _ _ (fun q => q @ p) _). Defined.
Global Instance isequiv_concat_lr {A : Type} {x x' y y' : A} (p : x' = x) (q : y = y')
  : IsEquiv (fun r:x=y => p @ r @ q) | 0. exact (@isequiv_compose _ _ (fun r => p @ r) _ _ (fun r => r @ q) _). Defined.
Definition equiv_concat_lr {A : Type} {x x' y y' : A} (p : x' = x) (q : y = y')
  : (x = y) <~> (x' = y'). exact (BuildEquiv _ _ (fun r:x=y => p @ r @ q) _). Defined.

Global Instance isequiv_whiskerL {A} {x y z : A} (p : x = y) {q r : y = z}
: IsEquiv (@whiskerL A x y z p q r).
Proof.
  refine (isequiv_adjointify _ _ _ _).
  -
 apply cancelL.
  -
 intros k.
unfold cancelL.
    rewrite !whiskerL_pp.
    refine ((_ @@ 1 @@ _) @ whiskerL_pVL p k).
    +
 destruct p, q; reflexivity.
    +
 destruct p, r; reflexivity.
  -
 intros k.
unfold cancelL.
    refine ((_ @@ 1 @@ _) @ whiskerL_VpL p k).
    +
 destruct p, q; reflexivity.
    +
 destruct p, r; reflexivity.
Defined.
Definition equiv_whiskerL {A} {x y z : A} (p : x = y) (q r : y = z)
: (q = r) <~> (p @ q = p @ r). exact (BuildEquiv _ _ (whiskerL p) _). Defined.
Definition equiv_cancelL {A} {x y z : A} (p : x = y) (q r : y = z)
: (p @ q = p @ r) <~> (q = r). exact (equiv_inverse (equiv_whiskerL p q r)). Defined.

Definition isequiv_cancelL {A} {x y z : A} (p : x = y) (q r : y = z)
  : IsEquiv (cancelL p q r).
Proof.
  change (IsEquiv (equiv_cancelL p q r)); exact _.
Defined.

Global Instance isequiv_whiskerR {A} {x y z : A} {p q : x = y} (r : y = z)
: IsEquiv (fun h => @whiskerR A x y z p q h r).
Proof.
  refine (isequiv_adjointify _ _ _ _).
  -
 apply cancelR.
  -
 intros k.
unfold cancelR.
    rewrite !whiskerR_pp.
    refine ((_ @@ 1 @@ _) @ whiskerR_VpR k r).
    +
 destruct p, r; reflexivity.
    +
 destruct q, r; reflexivity.
  -
 intros k.
unfold cancelR.
    refine ((_ @@ 1 @@ _) @ whiskerR_pVR k r).
    +
 destruct p, r; reflexivity.
    +
 destruct q, r; reflexivity.
Defined.
Definition equiv_whiskerR {A} {x y z : A} (p q : x = y) (r : y = z)
: (p = q) <~> (p @ r = q @ r). exact (BuildEquiv _ _ (fun h => whiskerR h r) _). Defined.
Definition equiv_cancelR {A} {x y z : A} (p q : x = y) (r : y = z)
: (p @ r = q @ r) <~> (p = q). exact (equiv_inverse (equiv_whiskerR p q r)). Defined.

Definition isequiv_cancelR {A} {x y z : A} (p q : x = y) (r : y = z)
  : IsEquiv (cancelR p q r).
Proof.
  change (IsEquiv (equiv_cancelR p q r)); exact _.
Defined.



Global Instance isequiv_moveR_Mp
 {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
: IsEquiv (moveR_Mp p q r).
Proof.
  destruct r.
  apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
Defined.
Definition equiv_moveR_Mp
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
: (p = r^ @ q) <~> (r @ p = q). exact (BuildEquiv _ _ (moveR_Mp p q r) _). Defined.

Global Instance isequiv_moveR_pM
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
: IsEquiv (moveR_pM p q r).
Proof.
  destruct p.
  apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
Defined.
Definition equiv_moveR_pM
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
: (r = q @ p^) <~> (r @ p = q). exact (BuildEquiv _ _ (moveR_pM p q r) _). Defined.

Global Instance isequiv_moveR_Vp
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y)
: IsEquiv (moveR_Vp p q r).
Proof.
  destruct r.
  apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
Defined.
Definition equiv_moveR_Vp
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y)
: (p = r @ q) <~> (r^ @ p = q). exact (BuildEquiv _ _ (moveR_Vp p q r) _). Defined.

Global Instance isequiv_moveR_pV
  {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x)
: IsEquiv (moveR_pV p q r).
Proof.
  destruct p.
  apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
Defined.
Definition equiv_moveR_pV
  {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x)
: (r = q @ p) <~> (r @ p^ = q). exact (BuildEquiv _ _ (moveR_pV p q r) _). Defined.

Global Instance isequiv_moveL_Mp
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
: IsEquiv (moveL_Mp p q r).
Proof.
  destruct r.
  apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
Defined.
Definition equiv_moveL_Mp
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
: (r^ @ q = p) <~> (q = r @ p). exact (BuildEquiv _ _ (moveL_Mp p q r) _). Defined.

Definition isequiv_moveL_pM
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x)
: IsEquiv (moveL_pM p q r).
Proof.
  destruct p.
  apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
Defined.
Definition equiv_moveL_pM
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : y = x) :
  q @ p^ = r <~> q = r @ p. exact (BuildEquiv _ _ _ (isequiv_moveL_pM p q r)). Defined.

Global Instance isequiv_moveL_Vp
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y)
: IsEquiv (moveL_Vp p q r).
Proof.
  destruct r.
  apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
Defined.
Definition equiv_moveL_Vp
  {A : Type} {x y z : A} (p : x = z) (q : y = z) (r : x = y)
: r @ q = p <~> q = r^ @ p. exact (BuildEquiv _ _ (moveL_Vp p q r) _). Defined.

Global Instance isequiv_moveL_pV
  {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x)
: IsEquiv (moveL_pV p q r).
Proof.
  destruct p.
  apply (isequiv_compose' _ (isequiv_concat_l _ _) _ (isequiv_concat_r _ _)).
Defined.
Definition equiv_moveL_pV
  {A : Type} {x y z : A} (p : z = x) (q : y = z) (r : y = x)
: q @ p = r <~> q = r @ p^. exact (BuildEquiv _ _ (moveL_pV p q r) _). Defined.

Definition isequiv_moveL_1M {A : Type} {x y : A} (p q : x = y)
: IsEquiv (moveL_1M p q).
Proof.
  destruct q.
apply isequiv_concat_l.
Defined.

Definition isequiv_moveL_M1 {A : Type} {x y : A} (p q : x = y)
: IsEquiv (moveL_M1 p q).
Proof.
  destruct q.
apply isequiv_concat_l.
Defined.

Definition isequiv_moveL_1V {A : Type} {x y : A} (p : x = y) (q : y = x)
: IsEquiv (moveL_1V p q).
Proof.
  destruct q.
apply isequiv_concat_l.
Defined.

Definition isequiv_moveL_V1 {A : Type} {x y : A} (p : x = y) (q : y = x)
: IsEquiv (moveL_V1 p q).
Proof.
  destruct q.
apply isequiv_concat_l.
Defined.

Definition isequiv_moveR_M1 {A : Type} {x y : A} (p q : x = y)
: IsEquiv (moveR_M1 p q).
Proof.
  destruct p.
apply isequiv_concat_r.
Defined.

Definition isequiv_moveR_1M {A : Type} {x y : A} (p q : x = y)
: IsEquiv (moveR_1M p q).
Proof.
  destruct p.
apply isequiv_concat_r.
Defined.

Definition isequiv_moveR_1V {A : Type} {x y : A} (p : x = y) (q : y = x)
: IsEquiv (moveR_1V p q).
Proof.
  destruct p.
apply isequiv_concat_r.
Defined.

Definition isequiv_moveR_V1 {A : Type} {x y : A} (p : x = y) (q : y = x)
: IsEquiv (moveR_V1 p q).
Proof.
  destruct p.
apply isequiv_concat_r.
Defined.

Global Instance isequiv_moveR_transport_p {A : Type} (P : A -> Type) {x y : A}
  (p : x = y) (u : P x) (v : P y)
: IsEquiv (moveR_transport_p P p u v).
Proof.
  destruct p.
apply isequiv_idmap.
Defined.
Definition equiv_moveR_transport_p {A : Type} (P : A -> Type) {x y : A}
  (p : x = y) (u : P x) (v : P y)
: u = transport P p^ v <~> transport P p u = v. exact (BuildEquiv _ _ (moveR_transport_p P p u v) _). Defined.

Global Instance isequiv_moveR_transport_V {A : Type} (P : A -> Type) {x y : A}
  (p : y = x) (u : P x) (v : P y)
: IsEquiv (moveR_transport_V P p u v).
Proof.
  destruct p.
apply isequiv_idmap.
Defined.
Definition equiv_moveR_transport_V {A : Type} (P : A -> Type) {x y : A}
  (p : y = x) (u : P x) (v : P y)
: u = transport P p v <~> transport P p^ u = v. exact (BuildEquiv _ _ (moveR_transport_V P p u v) _). Defined.

Global Instance isequiv_moveL_transport_V {A : Type} (P : A -> Type) {x y : A}
  (p : x = y) (u : P x) (v : P y)
: IsEquiv (moveL_transport_V P p u v).
Proof.
  destruct p.
apply isequiv_idmap.
Defined.
Definition equiv_moveL_transport_V {A : Type} (P : A -> Type) {x y : A}
  (p : x = y) (u : P x) (v : P y)
: transport P p u = v <~> u = transport P p^ v. exact (BuildEquiv _ _ (moveL_transport_V P p u v) _). Defined.

Global Instance isequiv_moveL_transport_p {A : Type} (P : A -> Type) {x y : A}
  (p : y = x) (u : P x) (v : P y)
: IsEquiv (moveL_transport_p P p u v).
Proof.
  destruct p.
apply isequiv_idmap.
Defined.
Definition equiv_moveL_transport_p {A : Type} (P : A -> Type) {x y : A}
  (p : y = x) (u : P x) (v : P y)
: transport P p^ u = v <~> u = transport P p v. exact (BuildEquiv _ _ (moveL_transport_p P p u v) _). Defined.

Global Instance isequiv_moveR_equiv_M `{IsEquiv A B f} (x : A) (y : B)
: IsEquiv (@moveR_equiv_M A B f _ x y).
Proof.
  unfold moveR_equiv_M.
  refine (@isequiv_compose _ _ (ap f) _ _ (fun q => q @ eisretr f y) _).
Defined.
Definition equiv_moveR_equiv_M `{IsEquiv A B f} (x : A) (y : B)
  : (x = f^-1 y) <~> (f x = y). exact (BuildEquiv _ _ (@moveR_equiv_M A B f _ x y) _). Defined.

Global Instance isequiv_moveR_equiv_V `{IsEquiv A B f} (x : B) (y : A)
: IsEquiv (@moveR_equiv_V A B f _ x y).
Proof.
  unfold moveR_equiv_V.
  refine (@isequiv_compose _ _ (ap f^-1) _ _ (fun q => q @ eissect f y) _).
Defined.
Definition equiv_moveR_equiv_V `{IsEquiv A B f} (x : B) (y : A)
  : (x = f y) <~> (f^-1 x = y). exact (BuildEquiv _ _ (@moveR_equiv_V A B f _ x y) _). Defined.

Global Instance isequiv_moveL_equiv_M `{IsEquiv A B f} (x : A) (y : B)
: IsEquiv (@moveL_equiv_M A B f _ x y).
Proof.
  unfold moveL_equiv_M.
  refine (@isequiv_compose _ _ (ap f) _ _ (fun q => (eisretr f y)^ @ q) _).
Defined.
Definition equiv_moveL_equiv_M `{IsEquiv A B f} (x : A) (y : B)
  : (f^-1 y = x) <~> (y = f x). exact (BuildEquiv _ _ (@moveL_equiv_M A B f _ x y) _). Defined.

Global Instance isequiv_moveL_equiv_V `{IsEquiv A B f} (x : B) (y : A)
: IsEquiv (@moveL_equiv_V A B f _ x y).
Proof.
  unfold moveL_equiv_V.
  refine (@isequiv_compose _ _ (ap f^-1) _ _ (fun q => (eissect f y)^ @ q) _).
Defined.
Definition equiv_moveL_equiv_V `{IsEquiv A B f} (x : B) (y : A)
  : (f y = x) <~> (y = f^-1 x). exact (BuildEquiv _ _ (@moveL_equiv_V A B f _ x y) _). Defined.





Definition dpath_path_l {A : Type} {x1 x2 y : A}
  (p : x1 = x2) (q : x1 = y) (r : x2 = y)
  : q = p @ r
  <~>
  transport (fun x => x = y) p q = r.
Proof.
  destruct p; simpl.
  exact (equiv_concat_r (concat_1p r) q).
Defined.

Definition dpath_path_r {A : Type} {x y1 y2 : A}
  (p : y1 = y2) (q : x = y1) (r : x = y2)
  : q @ p = r
  <~>
  transport (fun y => x = y) p q = r.
Proof.
  destruct p; simpl.
  exact (equiv_concat_l (concat_p1 q)^ r).
Defined.

Definition dpath_path_lr {A : Type} {x1 x2 : A}
  (p : x1 = x2) (q : x1 = x1) (r : x2 = x2)
  : q @ p = p @ r
  <~>
  transport (fun x => x = x) p q = r.
Proof.
  destruct p; simpl.
  refine (equiv_compose' (B := (q @ 1 = r)) _ _).
  exact (equiv_concat_l (concat_p1 q)^ r).
  exact (equiv_concat_r (concat_1p r) (q @ 1)).
Defined.

Definition dpath_path_Fl {A B : Type} {f : A -> B} {x1 x2 : A} {y : B}
  (p : x1 = x2) (q : f x1 = y) (r : f x2 = y)
  : q = ap f p @ r
  <~>
  transport (fun x => f x = y) p q = r.
Proof.
  destruct p; simpl.
  exact (equiv_concat_r (concat_1p r) q).
Defined.

Definition dpath_path_Fr {A B : Type} {g : A -> B} {x : B} {y1 y2 : A}
  (p : y1 = y2) (q : x = g y1) (r : x = g y2)
  : q @ ap g p = r
  <~>
  transport (fun y => x = g y) p q = r.
Proof.
  destruct p; simpl.
  exact (equiv_concat_l (concat_p1 q)^ r).
Defined.

Definition dpath_path_FlFr {A B : Type} {f g : A -> B} {x1 x2 : A}
  (p : x1 = x2) (q : f x1 = g x1) (r : f x2 = g x2)
  : q @ ap g p = ap f p @ r
  <~>
  transport (fun x => f x = g x) p q = r.
Proof.
  destruct p; simpl.
  refine (equiv_compose' (B := (q @ 1 = r)) _ _).
  exact (equiv_concat_l (concat_p1 q)^ r).
  exact (equiv_concat_r (concat_1p r) (q @ 1)).
Defined.

Definition dpath_path_FFlr {A B : Type} {f : A -> B} {g : B -> A}
  {x1 x2 : A} (p : x1 = x2) (q : g (f x1) = x1) (r : g (f x2) = x2)
  : q @ p = ap g (ap f p) @ r
  <~>
  transport (fun x => g (f x) = x) p q = r.
Proof.
  destruct p; simpl.
  refine (equiv_compose' (B := (q @ 1 = r)) _ _).
  exact (equiv_concat_l (concat_p1 q)^ r).
  exact (equiv_concat_r (concat_1p r) (q @ 1)).
Defined.

Definition dpath_path_lFFr {A B : Type} {f : A -> B} {g : B -> A}
  {x1 x2 : A} (p : x1 = x2) (q : x1 = g (f x1)) (r : x2 = g (f x2))
  : q @ ap g (ap f p) = p @ r
  <~>
  transport (fun x => x = g (f x)) p q = r.
Proof.
  destruct p; simpl.
  refine (equiv_compose' (B := (q @ 1 = r)) _ _).
  exact (equiv_concat_l (concat_p1 q)^ r).
  exact (equiv_concat_r (concat_1p r) (q @ 1)).
Defined.



Global Instance isequiv_paths_ind `{Funext} {A : Type} (a : A)
  (P : forall x, (a = x) -> Type)
  : IsEquiv (paths_ind a P) | 0
  := isequiv_adjointify (paths_ind a P) (fun f => f a 1) _ _.
Proof.
  -
 intros f.
    apply path_forall; intros x.
    apply path_forall; intros p.
    destruct p; reflexivity.
  -
 intros u.
reflexivity.
Defined.
Definition equiv_paths_ind `{Funext} {A : Type} (a : A)
  (P : forall x, (a = x) -> Type)
  : P a 1 <~> forall x p, P x p. exact (BuildEquiv _ _ (paths_ind a P) _). Defined.





End Paths.
Module Export Forall.
Import HoTT_DOT_Basics_DOT_Overture.
Import HoTT_DOT_Basics_DOT_Trunc.
Import HoTT_DOT_Basics.
Import HoTT_DOT_Basics_DOT_Trunc.HoTT.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.
Import HoTT_DOT_Basics.HoTT.
Import HoTT_DOT_Basics_DOT_Trunc.HoTT.Basics.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.Basics.

Import HoTT_DOT_Basics.HoTT.Basics.
Local Open Scope equiv_scope.

Generalizable Variables A B f g e n.

Section AssumeFunext.
Context `{Funext}.
Definition apD10_path_forall `{P : A -> Type}
  (f g : forall x, P x) (h : f == g)
  : apD10 (path_forall _ _ h) == h. exact (apD10 (eisretr apD10 h)). Defined.
Definition eta_path_forall `{P : A -> Type}
  (f g : forall x, P x) (p : f = g)
  : path_forall _ _ (apD10 p) = p. exact (eissect apD10 p). Defined.
Definition path_forall_1 `{P : A -> Type} (f : forall x, P x)
  : (path_forall f f (fun x => 1)) = 1. exact (eta_path_forall f f 1). Defined.



Definition equiv_apD10 `{Funext} {A : Type} (P : A -> Type) f g
: (f = g) <~> (f == g)
  := BuildEquiv _ _ (@apD10 A P f g) _.
Global Instance isequiv_path_forall `{P : A -> Type} (f g : forall x, P x)
  : IsEquiv (path_forall f g) | 0. exact (@isequiv_inverse _ _ (@apD10 A P f g) _). Defined.
Definition equiv_path_forall `{P : A -> Type} (f g : forall x, P x)
  : (f == g)  <~>  (f = g). exact (BuildEquiv _ _ (path_forall f g) _). Defined.




Definition transport_forall
  {A : Type} {P : A -> Type} {C : forall x, P x -> Type}
  {x1 x2 : A} (p : x1 = x2) (f : forall y : P x1, C x1 y)
  : (transport (fun x => forall y : P x, C x y) p f)
    == (fun y =>
       transport (C x2) (transport_pV _ _ _) (transportD _ _ p _ (f (p^ # y))))
  := match p with idpath => fun _ => 1 end.


Definition transport_forall_constant
  {A B : Type} {C : A -> B -> Type}
  {x1 x2 : A} (p : x1 = x2) (f : forall y : B, C x1 y)
  : (transport (fun x => forall y : B, C x y) p f)
    == (fun y => transport (fun x => C x y) p (f y))
  := match p with idpath => fun _ => 1 end.




Definition ap_lambdaD {A B : Type} {C : B -> Type} {x y : A} (p : x = y) (M : forall a b, C b) :
  ap (fun a b => M a b) p =
  path_forall _ _ (fun b => ap (fun a => M a b) p).
Proof.
  destruct p;
  symmetry;
  simpl; apply path_forall_1.
Defined.





Definition dpath_forall `{Funext}
  {A:Type} (B:A -> Type) (C:forall a, B a -> Type) (x1 x2:A) (p:x1=x2)
  (f:forall y1:B x1, C x1 y1) (g:forall (y2:B x2), C x2 y2)
  : (forall (y1:B x1), transportD B C p y1 (f y1) = g (transport B p y1))
  <~>
  (transport (fun x => forall y:B x, C x y) p f = g).
Proof.
  destruct p.
  apply equiv_path_forall.
Defined.
Definition functor_forall `{P : A -> Type} `{Q : B -> Type}
    (f0 : B -> A) (f1 : forall b:B, P (f0 b) -> Q b)
  : (forall a:A, P a) -> (forall b:B, Q b). exact ((fun g b => f1 _ (g (f0 b)))). Defined.

Definition ap_functor_forall `{P : A -> Type} `{Q : B -> Type}
    (f0 : B -> A) (f1 : forall b:B, P (f0 b) -> Q b)
    (g g' : forall a:A, P a) (h : g == g')
  : ap (functor_forall f0 f1) (path_forall _ _ h)
    = path_forall _ _ (fun b:B => (ap (f1 b) (h (f0 b)))).
Proof.
  revert h.
 equiv_intro (@apD10 A P g g') h.
  destruct h.
 simpl.
  transitivity (idpath (functor_forall f0 f1 g)).
  -
 exact (ap (ap (functor_forall f0 f1)) (path_forall_1 g)).
  -
 symmetry.
 apply path_forall_1.
Defined.



Global Instance isequiv_functor_forall `{P : A -> Type} `{Q : B -> Type}
  `{IsEquiv B A f} `{forall b, @IsEquiv (P (f b)) (Q b) (g b)}
  : IsEquiv (functor_forall f g) | 1000.
Proof.
  refine (isequiv_adjointify (functor_forall f g)
    (functor_forall (f^-1)
      (fun (x:A) (y:Q (f^-1 x)) => eisretr f x # (g (f^-1 x))^-1 y
      )) _ _);
  intros h.
  -
 abstract (
        apply path_forall; intros b; unfold functor_forall;
        rewrite eisadj;
        rewrite <- transport_compose;
        rewrite ap_transport;
        rewrite eisretr;
        apply apD
      ).
  -
 abstract (
        apply path_forall; intros a; unfold functor_forall;
        rewrite eissect;
        apply apD
      ).
Defined.
Definition equiv_functor_forall `{P : A -> Type} `{Q : B -> Type}
  (f : B -> A) `{IsEquiv B A f}
  (g : forall b, P (f b) -> Q b)
  `{forall b, @IsEquiv (P (f b)) (Q b) (g b)}
  : (forall a, P a) <~> (forall b, Q b). exact (BuildEquiv _ _ (functor_forall f g) _). Defined.
Definition equiv_functor_forall' `{P : A -> Type} `{Q : B -> Type}
  (f : B <~> A) (g : forall b, P (f b) <~> Q b)
  : (forall a, P a) <~> (forall b, Q b). exact (equiv_functor_forall f g). Defined.
Definition equiv_functor_forall_id `{P : A -> Type} `{Q : A -> Type}
  (g : forall a, P a <~> Q a)
  : (forall a, P a) <~> (forall a, Q a). exact (equiv_functor_forall (equiv_idmap A) g). Defined.



Global Instance contr_forall `{P : A -> Type} `{forall a, Contr (P a)}
  : Contr (forall a, P a) | 100.
Proof.
  exists (fun a => center (P a)).
  intro f.
 apply path_forall.
 intro a.
 apply contr.
Defined.

Global Instance trunc_forall `{P : A -> Type} `{forall a, IsTrunc n (P a)}
  : IsTrunc n (forall a, P a) | 100.
Proof.
  generalize dependent P.
  induction n as [ | n' IH]; simpl; intros P ?.

  -
 exact _.

  -
 intros f g; apply (trunc_equiv _ (apD10 ^-1)).
Defined.
Definition flip `{P : A -> B -> Type}
  : (forall a b, P a b) -> (forall b a, P a b). exact (fun f b a => f a b). Defined.

Global Instance isequiv_flip `{P : A -> B -> Type}
  : IsEquiv (@flip _ _ P) | 0.
Proof.
  set (flip_P := @flip _ _ P).
  set (flip_P_inv := @flip _ _ (flip P)).
  set (flip_P_is_sect := (fun f => 1) : Sect flip_P flip_P_inv).
  set (flip_P_is_retr := (fun g => 1) : Sect flip_P_inv flip_P).
  exists flip_P_inv flip_P_is_retr flip_P_is_sect.
  intro g.
 exact 1.
Defined.
Definition equiv_flip `(P : A -> B -> Type)
  : (forall a b, P a b) <~> (forall b a, P a b). exact (BuildEquiv _ _ (@flip _ _ P) _). Defined.

End AssumeFunext.

End Forall.
Module Export Arrow.
Import HoTT_DOT_Basics_DOT_Overture.
Import HoTT_DOT_Basics_DOT_Trunc.
Import HoTT_DOT_Basics.
Import HoTT_DOT_Basics_DOT_Trunc.HoTT.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.
Import HoTT_DOT_Basics.HoTT.
Import HoTT_DOT_Basics_DOT_Trunc.HoTT.Basics.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.Basics.

Import HoTT_DOT_Basics.HoTT.Basics.
Local Open Scope equiv_scope.

Generalizable Variables A B C D f g n.

Section AssumeFunext.
Context `{Funext}.
Definition path_arrow {A B : Type} (f g : A -> B)
  : (f == g) -> (f = g). exact (path_forall f g). Defined.
Definition ap10_path_arrow {A B : Type} (f g : A -> B) (h : f == g)
  : ap10 (path_arrow f g h) == h. exact (apD10_path_forall f g h). Defined.
Definition apD10_path_arrow {A B : Type} (f g : A -> B) (h : f == g)
  : apD10 (path_arrow f g h) == h. exact (apD10_path_forall f g h). Defined.
Definition ap10_path_forall {A B : Type} (f g : A -> B) (h : f == g)
  : ap10 (path_forall f g h) == h. exact (apD10_path_forall f g h). Defined.
Definition eta_path_arrow {A B : Type} (f g : A -> B) (p : f = g)
  : path_arrow f g (ap10 p) = p. exact (eta_path_forall f g p). Defined.
Definition path_arrow_1 {A B : Type} (f : A -> B)
  : (path_arrow f f (fun x => 1)) = 1. exact (eta_path_arrow f f 1). Defined.

Definition equiv_ap10 `{Funext} {A B : Type} f g
: (f = g) <~> (f == g)
  := BuildEquiv _ _ (@ap10 A B f g) _.
Global Instance isequiv_path_arrow {A B : Type} (f g : A -> B)
  : IsEquiv (path_arrow f g) | 0. exact (isequiv_path_forall f g). Defined.
Definition equiv_path_arrow {A B : Type} (f g : A -> B)
  : (f == g) <~> (f = g). exact (equiv_path_forall f g). Defined.





Definition transport_arrow {A : Type} {B C : A -> Type}
  {x1 x2 : A} (p : x1 = x2) (f : B x1 -> C x1) (y : B x2)
  : (transport (fun x => B x -> C x) p f) y  =  p # (f (p^ # y)).
Proof.
  destruct p; simpl; auto.
Defined.

Definition transport_arrow_toconst {A : Type} {B : A -> Type} {C : Type}
  {x1 x2 : A} (p : x1 = x2) (f : B x1 -> C) (y : B x2)
  : (transport (fun x => B x -> C) p f) y  =  f (p^ # y).
Proof.
  destruct p; simpl; auto.
Defined.

Definition transport_arrow_fromconst {A B : Type} {C : A -> Type}
  {x1 x2 : A} (p : x1 = x2) (f : B -> C x1) (y : B)
  : (transport (fun x => B -> C x) p f) y  =  p # (f y).
Proof.
  destruct p; simpl; auto.
Defined.



Definition ap_transport_arrow_toconst {A : Type} {B : A -> Type} {C : Type}
  {x1 x2 : A} (p : x1 = x2) (f : B x1 -> C) {y1 y2 : B x2} (q : y1 = y2)
  : ap (transport (fun x => B x -> C) p f) q
    @ transport_arrow_toconst p f y2
    = transport_arrow_toconst p f y1
    @ ap (fun y => f (p^ # y)) q.
Proof.
  destruct p, q; reflexivity.
Defined.





Definition dpath_arrow
  {A:Type} (B C : A -> Type) {x1 x2:A} (p:x1=x2)
  (f : B x1 -> C x1) (g : B x2 -> C x2)
  : (forall (y1:B x1), transport C p (f y1) = g (transport B p y1))
  <~>
  (transport (fun x => B x -> C x) p f = g).
Proof.
  destruct p.
  apply equiv_path_arrow.
Defined.

Definition ap10_dpath_arrow
  {A:Type} (B C : A -> Type) {x1 x2:A} (p:x1=x2)
  (f : B x1 -> C x1) (g : B x2 -> C x2)
  (h : forall (y1:B x1), transport C p (f y1) = g (transport B p y1))
  (u : B x1)
  : ap10 (dpath_arrow B C p f g h) (p # u)
  = transport_arrow p f (p # u)
  @ ap (fun x => p # (f x)) (transport_Vp B p u)
  @ h u.
Proof.
  destruct p; simpl; unfold ap10.
  exact (apD10_path_forall f g h u @ (concat_1p _)^).
Defined.
Definition ap_apply_l {A B : Type} {x y : A -> B} (p : x = y) (z : A) :
  ap (fun f => f z) p = ap10 p z.
admit.
Defined.

Definition ap_apply_Fl {A B C : Type} {x y : A} (p : x = y) (M : A -> B -> C) (z : B) :
  ap (fun a => (M a) z) p = ap10 (ap M p) z
:= match p with 1 => 1 end.
Definition ap_apply_Fr {A B C : Type} {x y : A} (p : x = y) (z : B -> C) (N : A -> B) :
  ap (fun a => z (N a)) p = ap01 z (ap N p). exact ((ap_compose N _ _)). Defined.

Definition ap_apply_FlFr {A B C : Type} {x y : A} (p : x = y) (M : A -> B -> C) (N : A -> B) :
  ap (fun a => (M a) (N a)) p = ap11 (ap M p) (ap N p)
:= match p with 1 => 1 end.


Definition ap_lambda {A B C : Type} {x y : A} (p : x = y) (M : A -> B -> C) :
  ap (fun a b => M a b) p =
  path_arrow _ _ (fun b => ap (fun a => M a b) p).
Proof.
  destruct p;
  symmetry;
  simpl; apply path_arrow_1.
Defined.
Definition functor_arrow `(f : B -> A) `(g : C -> D)
  : (A -> C) -> (B -> D). exact (@functor_forall A (fun _ => C) B (fun _ => D) f (fun _ => g)). Defined.
Definition ap_functor_arrow `(f : B -> A) `(g : C -> D)
  (h h' : A -> C) (p : h == h')
  : ap (functor_arrow f g) (path_arrow _ _ p)
  = path_arrow _ _ (fun b => ap g (p (f b))). exact (@ap_functor_forall _ A (fun _ => C) B (fun _ => D)
  f (fun _ => g) h h' p). Defined.
Global Instance contr_arrow {A B : Type} `{Contr B}
  : Contr (A -> B) | 100. exact (contr_forall). Defined.
Global Instance trunc_arrow {A B : Type} `{IsTrunc n B}
  : IsTrunc n (A -> B) | 100. exact (trunc_forall). Defined.
Global Instance isequiv_functor_arrow `{IsEquiv B A f} `{IsEquiv C D g}
  : IsEquiv (functor_arrow f g) | 1000. exact (@isequiv_functor_forall _ A (fun _ => C) B (fun _ => D)
     _ _ _ _). Defined.
Definition equiv_functor_arrow `{IsEquiv B A f} `{IsEquiv C D g}
  : (A -> C) <~> (B -> D). exact (@equiv_functor_forall _ A (fun _ => C) B (fun _ => D)
  f _ (fun _ => g) _). Defined.
Definition equiv_functor_arrow' `(f : B <~> A) `(g : C <~> D)
  : (A -> C) <~> (B -> D). exact (@equiv_functor_forall' _ A (fun _ => C) B (fun _ => D)
  f (fun _ => g)). Defined.



End AssumeFunext.

End Arrow.
Module Export Prod.
Import HoTT_DOT_Basics_DOT_Overture.
Import HoTT_DOT_Basics_DOT_Trunc.
Import HoTT_DOT_Basics.
Import HoTT_DOT_Basics_DOT_Trunc.HoTT.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.
Import HoTT_DOT_Basics.HoTT.
Import HoTT_DOT_Basics_DOT_Trunc.HoTT.Basics.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.Basics.

Import HoTT_DOT_Basics.HoTT.Basics.
Local Open Scope equiv_scope.
Generalizable Variables X A B f g n.

Scheme prod_ind := Induction for prod Sort Type.
Arguments prod_ind {A B} P f p.
Definition unpack_prod `{P : A * B -> Type} (u : A * B) :
  P (fst u, snd u) -> P u.
admit.
Defined.
Definition pack_prod `{P : A * B -> Type} (u : A * B) :
  P u -> P (fst u, snd u).
admit.
Defined.
Definition eta_prod `(z : A * B) : (fst z, snd z) = z. exact (1). Defined.

Arguments eta_prod / .




Definition path_prod_uncurried {A B : Type} (z z' : A * B)
  (pq : (fst z = fst z') * (snd z = snd z'))
  : (z = z').
Proof.
  change ((fst z, snd z) = (fst z', snd z')).
  case (fst pq).
case (snd pq).
  reflexivity.
Defined.
Definition path_prod {A B : Type} (z z' : A * B) :
  (fst z = fst z') -> (snd z = snd z') -> (z = z'). exact (fun p q => path_prod_uncurried z z' (p,q)). Defined.
Definition path_prod' {A B : Type} {x x' : A} {y y' : B}
  : (x = x') -> (y = y') -> ((x,y) = (x',y')). exact (fun p q => path_prod (x,y) (x',y') p q). Defined.



Definition ap_fst_path_prod {A B : Type} {z z' : A * B}
  (p : fst z = fst z') (q : snd z = snd z') :
  ap fst (path_prod _ _ p q) = p.
Proof.
  change z with (fst z, snd z).
  change z' with (fst z', snd z').
  destruct p, q.
  reflexivity.
Defined.

Definition ap_snd_path_prod {A B : Type} {z z' : A * B}
  (p : fst z = fst z') (q : snd z = snd z') :
  ap snd (path_prod _ _ p q) = q.
Proof.
  change z with (fst z, snd z).
  change z' with (fst z', snd z').
  destruct p, q.
  reflexivity.
Defined.

Definition eta_path_prod {A B : Type} {z z' : A * B} (p : z = z') :
  path_prod _ _(ap fst p) (ap snd p) = p.
Proof.
  destruct p.
reflexivity.
Defined.



Lemma transport_path_prod_uncurried {A B} (P : A * B -> Type) {x y : A * B}
      (H : (fst x = fst y) * (snd x = snd y))
      (Px : P x)
: transport P (path_prod_uncurried _ _ H) Px
  = transport (fun x => P (x, snd y))
              (fst H)
              (transport (fun y => P (fst x, y))
                         (snd H)
                         Px).
admit.
Defined.
Definition transport_path_prod {A B} (P : A * B -> Type) {x y : A * B}
           (HA : fst x = fst y)
           (HB : snd x = snd y)
           (Px : P x)
: transport P (path_prod _ _ HA HB) Px
  = transport (fun x => P (x, snd y))
              HA
              (transport (fun y => P (fst x, y))
                         HB
                         Px).
admit.
Defined.
Definition transport_path_prod'
           {A B} (P : A * B -> Type)
           {x y : A}
           {x' y' : B}
           (HA : x = y)
           (HB : x' = y')
           (Px : P (x,x'))
: transport P (path_prod' HA HB) Px
  = transport (fun x => P (x, y'))
              HA
              (transport (fun y => P (x, y))
                         HB
                         Px). exact (@transport_path_prod _ _ P (x, x') (y, y') HA HB Px). Defined.



Global Instance isequiv_path_prod {A B : Type} {z z' : A * B}
: IsEquiv (path_prod_uncurried z z') | 0
  := BuildIsEquiv
       _ _ _
       (fun r => (ap fst r, ap snd r))
       eta_path_prod
       (fun pq => path_prod'
                    (ap_fst_path_prod (fst pq) (snd pq))
                    (ap_snd_path_prod (fst pq) (snd pq)))
       _.
Proof.
  destruct z as [x y], z' as [x' y'].
  intros [p q]; simpl in p, q.
  destruct p, q; reflexivity.
Defined.
Definition equiv_path_prod {A B : Type} (z z' : A * B)
  : (fst z = fst z') * (snd z = snd z')  <~>  (z = z').
admit.
Defined.



Definition transport_prod {A : Type} {P Q : A -> Type} {a a' : A} (p : a = a')
  (z : P a * Q a)
  : transport (fun a => P a * Q a) p z  =  (p # (fst z), p # (snd z))
  := match p with idpath => 1 end.
Definition functor_prod {A A' B B' : Type} (f:A->A') (g:B->B')
  : A * B -> A' * B'. exact (fun z => (f (fst z), g (snd z))). Defined.

Definition ap_functor_prod {A A' B B' : Type} (f:A->A') (g:B->B')
  (z z' : A * B) (p : fst z = fst z') (q : snd z = snd z')
  : ap (functor_prod f g) (path_prod _ _ p q)
  = path_prod (functor_prod f g z) (functor_prod f g z') (ap f p) (ap g q).
Proof.
  destruct z as [a b]; destruct z' as [a' b'].
  simpl in p, q.
destruct p, q.
reflexivity.
Defined.



Global Instance isequiv_functor_prod `{IsEquiv A A' f} `{IsEquiv B B' g}
: IsEquiv (functor_prod f g) | 1000
  := BuildIsEquiv
       _ _ (functor_prod f g) (functor_prod f^-1 g^-1)
       (fun z => path_prod' (eisretr f (fst z)) (eisretr g (snd z)) @ eta_prod z)
       (fun w => path_prod' (eissect f (fst w)) (eissect g (snd w)) @ eta_prod w)
       _.
Proof.
  intros [a b]; simpl.
  unfold path_prod'.
  rewrite !concat_p1.
  rewrite ap_functor_prod.
  rewrite !eisadj.
  reflexivity.
Defined.

Definition equiv_functor_prod `{IsEquiv A A' f} `{IsEquiv B B' g}
  : A * B <~> A' * B'.
Proof.
  exists (functor_prod f g).
  exact _.

Defined.

Definition equiv_functor_prod' {A A' B B' : Type} (f : A <~> A') (g : B <~> B')
  : A * B <~> A' * B'.
Proof.
  exists (functor_prod f g).
  exact _.
Defined.

Definition equiv_functor_prod_l {A B B' : Type} (g : B <~> B')
  : A * B <~> A * B'.
Proof.
  exists (functor_prod idmap g).
  exact _.
Defined.

Definition equiv_functor_prod_r {A A' B : Type} (f : A <~> A')
  : A * B <~> A' * B.
Proof.
  exists (functor_prod f idmap).
  exact _.
Defined.
Definition equiv_prod_symm (A B : Type) : A * B <~> B * A. exact (BuildEquiv
       _ _ _
       (BuildIsEquiv
          (A*B) (B*A)
          (fun ab => (snd ab, fst ab))
          (fun ba => (snd ba, fst ba))
          (fun _ => 1)
          (fun _ => 1)
          (fun _ => 1))). Defined.
Definition equiv_prod_assoc (A B C : Type) : A * (B * C) <~> (A * B) * C. exact (BuildEquiv
       _ _ _
       (BuildIsEquiv
          (A * (B * C)) ((A * B) * C)
          (fun abc => ((fst abc, fst (snd abc)), snd (snd abc)))
          (fun abc => (fst (fst abc), (snd (fst abc), snd abc)))
          (fun _ => 1)
          (fun _ => 1)
          (fun _ => 1))). Defined.
Global Instance isequiv_prod_ind `(P : A * B -> Type)
: IsEquiv (prod_ind P) | 0. exact (BuildIsEquiv
       _ _
       (prod_ind P)
       (fun f x y => f (x, y))
       (fun _ => 1)
       (fun _ => 1)
       (fun _ => 1)). Defined.
Definition equiv_prod_ind `(P : A * B -> Type)
  : (forall (a : A) (b : B), P (a, b)) <~> (forall p : A * B, P p). exact (BuildEquiv _ _ (prod_ind P) _). Defined.
Definition equiv_uncurry (A B C : Type)
  : (A -> B -> C) <~> (A * B -> C). exact (equiv_prod_ind (fun _ => C)). Defined.
Definition prod_coind_uncurried `{A : X -> Type} `{B : X -> Type}
  : (forall x, A x) * (forall x, B x) -> (forall x, A x * B x). exact (fun fg x => (fst fg x, snd fg x)). Defined.
Definition prod_coind `(f : forall x:X, A x) `(g : forall x:X, B x)
  : forall x, A x * B x. exact (prod_coind_uncurried (f, g)). Defined.
Global Instance isequiv_prod_coind `(A : X -> Type) (B : X -> Type)
: IsEquiv (@prod_coind_uncurried X A B) | 0. exact (BuildIsEquiv
       _ _
       (@prod_coind_uncurried X A B)
       (fun h => (fun x => fst (h x), fun x => snd (h x)))
       (fun _ => 1)
       (fun _ => 1)
       (fun _ => 1)). Defined.
Definition equiv_prod_coind `(A : X -> Type) (B : X -> Type)
  : ((forall x, A x) * (forall x, B x)) <~> (forall x, A x * B x). exact (BuildEquiv _ _ (@prod_coind_uncurried X A B) _). Defined.



Global Instance trunc_prod `{IsTrunc n A} `{IsTrunc n B} : IsTrunc n (A * B) | 100.
Proof.
  generalize dependent B; generalize dependent A.
  induction n as [| n I]; simpl; (intros A ? B ?).
  {
 exists (center A, center B).
    intros z; apply path_prod; apply contr.
}
  {
 intros x y.
    exact (trunc_equiv _ (equiv_path_prod x y)).
}
Defined.
Global Instance contr_prod `{CA : Contr A} `{CB : Contr B} : Contr (A * B) | 100. exact (@trunc_prod -2 A CA B CB). Defined.

End Prod.
Module Export Unit.
Import HoTT_DOT_Basics_DOT_Overture.
Import HoTT_DOT_Basics_DOT_Trunc.
Import HoTT_DOT_Basics.
Import HoTT_DOT_Basics_DOT_Trunc.HoTT.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.
Import HoTT_DOT_Basics.HoTT.
Import HoTT_DOT_Basics_DOT_Trunc.HoTT.Basics.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.Basics.

Import HoTT_DOT_Basics.HoTT.Basics.
Local Open Scope equiv_scope.
Generalizable Variables A.
Definition eta_unit (z : Unit) : tt = z.
admit.
Defined.
Definition path_unit_uncurried (z z' : Unit) : Unit -> z = z'. exact (fun _ => match z, z' with tt, tt => 1 end). Defined.
Definition path_unit (z z' : Unit) : z = z'. exact (path_unit_uncurried z z' tt). Defined.

Definition eta_path_unit {z z' : Unit} (p : z = z') :
  path_unit z z' = p.
Proof.
  destruct p.
destruct z.
reflexivity.
Defined.

Global Instance isequiv_path_unit (z z' : Unit) : IsEquiv (path_unit_uncurried z z') | 0.
  refine (BuildIsEquiv _ _ (path_unit_uncurried z z') (fun _ => tt)
    (fun p:z=z' =>
      match p in (_ = z') return (path_unit_uncurried z z' tt = p) with
        | idpath => match z as z return (path_unit_uncurried z z tt = 1) with
                    | tt => 1
                  end
      end)
    (fun x => match x with tt => 1 end) _).
  intros []; destruct z, z'; reflexivity.
Defined.
Definition equiv_path_unit (z z' : Unit) : Unit <~> (z = z'). exact (BuildEquiv _ _ (path_unit_uncurried z z') _). Defined.
Global Instance isequiv_unit_ind `{Funext} (A : Type) : IsEquiv (@Unit_ind (fun _ => A)) | 0. exact (isequiv_adjointify _
  (fun f : Unit -> A => f tt)
  (fun f : Unit -> A => path_forall (@Unit_ind (fun _ => A) (f tt)) f
                                    (fun x => match x with tt => 1 end))
  (fun _ => 1)). Defined.


Notation unit_name x := (fun (_ : Unit) => x).

Global Instance isequiv_unit_name `{Funext} (A : Type)
: IsEquiv (fun (a:A) => unit_name a).
Proof.
  refine (isequiv_adjointify _ (fun f => f tt) _ _).
  -
 intros f; apply path_forall; intros x.
    apply ap, path_unit.
  -
 intros a; reflexivity.
Defined.
Definition unit_coind {A : Type} : Unit -> (A -> Unit).
admit.
Defined.

Global Instance isequiv_unit_coind `{Funext} (A : Type) : IsEquiv (@unit_coind A) | 0
  := isequiv_adjointify _
  (fun f => tt)
  _ _.
Proof.
  -
 intro f.
apply path_forall; intros x; apply path_unit.
  -
 intro x; destruct x; reflexivity.
Defined.
Definition equiv_unit_coind `{Funext} (A : Type)
  : Unit <~> (A -> Unit). exact (BuildEquiv _ _ (@unit_coind A) _). Defined.
Global Instance contr_unit : Contr Unit | 0. exact (let x := {|
  center := tt;
  contr := fun t : Unit => match t with tt => 1 end
|} in x). Defined.




Definition equiv_contr_unit `{Contr A} : A <~> Unit.
Proof.
  refine (BuildEquiv _ _
    (fun (_ : A) => tt)
    (BuildIsEquiv _ _ _
      (fun (_ : Unit) => center A)
      (fun t : Unit => match t with tt => 1 end)
      (fun x : A => contr x) _)).
  intro x.
symmetry; apply ap_const.
Defined.
Global Instance contr_equiv_unit (A : Type) (f : A <~> Unit) : Contr A | 10000. exact (BuildContr A (f^-1 tt)
  (fun a => ap f^-1 (contr (f a)) @ eissect f a)). Defined.

End Unit.
Module Export Sigma.
Import HoTT_DOT_Basics_DOT_Overture.
Import HoTT_DOT_Basics_DOT_Trunc.
Import HoTT_DOT_Basics.
Import HoTT_DOT_Basics_DOT_Trunc.HoTT.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.
Import HoTT_DOT_Basics.HoTT.
Import HoTT_DOT_Basics_DOT_Trunc.HoTT.Basics.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.Basics.

Import HoTT_DOT_Basics.HoTT.Basics.
Local Open Scope equiv_scope.

Generalizable Variables X A B C f g n.

Scheme sig_ind := Induction for sig Sort Type.
Scheme sig_rec := Minimality for sig Sort Type.
Definition unpack_sigma `{P : A -> Type} (Q : sigT P -> Type) (u : sigT P)
: Q (u.1; u.2) -> Q u.
admit.
Defined.
Definition eta_sigma `{P : A -> Type} (u : sigT P)
  : (u.1; u.2) = u. exact (1). Defined.
Definition eta2_sigma `{P : forall (a : A) (b : B a), Type}
           (u : sigT (fun a => sigT (P a)))
  : (u.1; (u.2.1; u.2.2)) = u.
admit.
Defined.
Definition eta3_sigma `{P : forall (a : A) (b : B a) (c : C a b), Type}
           (u : sigT (fun a => sigT (fun b => sigT (P a b))))
  : (u.1; (u.2.1; (u.2.2.1; u.2.2.2))) = u. exact (1). Defined.
Definition path_sigma_uncurried {A : Type} (P : A -> Type) (u v : sigT P)
           (pq : {p : u.1 = v.1 &  p # u.2 = v.2})
: u = v. exact (match pq.2 in (_ = v2) return u = (v.1; v2) with
       | 1 => match pq.1 as p in (_ = v1) return u = (v1; p # u.2) with
                | 1 => 1
              end
     end). Defined.
Definition path_sigma {A : Type} (P : A -> Type) (u v : sigT P)
           (p : u.1 = v.1) (q : p # u.2 = v.2)
: u = v. exact (path_sigma_uncurried P u v (p;q)). Defined.



Definition dpath_forall'
           {A : Type } (P : A -> Type) (Q: sigT P -> Type) {x y : A} (h : x = y)
           (f : forall p, Q (x ; p)) (g : forall p, Q (y ; p))
:
  (forall p, transport Q (path_sigma P (x ; p) (y; _) h 1) (f p) = g (h # p))
    <~>
    (forall p, transportD P (fun x => fun p => Q ( x ; p)) h p (f p) = g (transport P h p)).
Proof.
  destruct h.
  apply equiv_idmap.
Defined.
Definition path_sigma' {A : Type} (P : A -> Type) {x x' : A} {y : P x} {y' : P x'}
           (p : x = x') (q : p # y = y')
: (x;y) = (x';y'). exact (path_sigma P (x;y) (x';y') p q). Defined.
Definition pr1_path `{P : A -> Type} {u v : sigT P} (p : u = v)
: u.1 = v.1. exact (ap pr1 p). Defined.


Notation "p ..1" := (pr1_path p) (at level 3) : fibration_scope.
Definition pr2_path `{P : A -> Type} {u v : sigT P} (p : u = v)
: p..1 # u.2 = v.2. exact ((transport_compose P pr1 p u.2)^
     @ (@apD {x:A & P x} _ pr2 _ _ p)). Defined.

Notation "p ..2" := (pr2_path p) (at level 3) : fibration_scope.



Definition pr1_path_sigma_uncurried `{P : A -> Type} {u v : sigT P}
           (pq : { p : u.1 = v.1 & p # u.2 = v.2 })
: (path_sigma_uncurried _ _ _ pq)..1 = pq.1.
Proof.
  destruct u as [u1 u2]; destruct v as [v1 v2]; simpl in *.
  destruct pq as [p q].
  destruct p; simpl in q; destruct q; reflexivity.
Defined.

Definition pr2_path_sigma_uncurried `{P : A -> Type} {u v : sigT P}
           (pq : { p : u.1 = v.1 & p # u.2 = v.2 })
: (path_sigma_uncurried _ _ _ pq)..2
  = ap (fun s => transport P s u.2) (pr1_path_sigma_uncurried pq) @ pq.2.
Proof.
  destruct u as [u1 u2]; destruct v as [v1 v2]; simpl in *.
  destruct pq as [p q].
  destruct p; simpl in q; destruct q; reflexivity.
Defined.

Definition eta_path_sigma_uncurried `{P : A -> Type} {u v : sigT P}
           (p : u = v)
: path_sigma_uncurried _ _ _ (p..1; p..2) = p.
Proof.
  destruct p.
reflexivity.
Defined.

Lemma transport_pr1_path_sigma_uncurried
      `{P : A -> Type} {u v : sigT P}
      (pq : { p : u.1 = v.1 & transport P p u.2 = v.2 })
      Q
: transport (fun x => Q x.1) (@path_sigma_uncurried A P u v pq)
  = transport _ pq.1.
admit.
Defined.
Definition pr1_path_sigma `{P : A -> Type} {u v : sigT P}
           (p : u.1 = v.1) (q : p # u.2 = v.2)
: (path_sigma _ _ _ p q)..1 = p. exact (pr1_path_sigma_uncurried (p; q)). Defined.
Definition pr2_path_sigma `{P : A -> Type} {u v : sigT P}
           (p : u.1 = v.1) (q : p # u.2 = v.2)
: (path_sigma _ _ _ p q)..2
  = ap (fun s => transport P s u.2) (pr1_path_sigma p q) @ q. exact (pr2_path_sigma_uncurried (p; q)). Defined.
Definition eta_path_sigma `{P : A -> Type} {u v : sigT P} (p : u = v)
: path_sigma _ _ _ (p..1) (p..2) = p. exact (eta_path_sigma_uncurried p). Defined.
Definition transport_pr1_path_sigma
           `{P : A -> Type} {u v : sigT P}
           (p : u.1 = v.1) (q : p # u.2 = v.2)
           Q
: transport (fun x => Q x.1) (@path_sigma A P u v p q)
  = transport _ p. exact (transport_pr1_path_sigma_uncurried (p; q) Q). Defined.



Global Instance isequiv_path_sigma `{P : A -> Type} {u v : sigT P}
: IsEquiv (path_sigma_uncurried P u v) | 0
  := BuildIsEquiv
       _ _
       _ (fun r => (r..1; r..2))
       eta_path_sigma
       _ _.
Proof.
  all: destruct u, v; intros [p q].
  all: simpl in *.
  all: destruct q, p; simpl in *.
  all: reflexivity.
Defined.
Definition equiv_path_sigma `(P : A -> Type) (u v : sigT P)
: {p : u.1 = v.1 &  p # u.2 = v.2} <~> (u = v). exact (BuildEquiv _ _ (path_sigma_uncurried P u v) _). Defined.



Definition path_sigma_pp_pp {A : Type} (P : A -> Type) {u v w : sigT P}
           (p1 : u.1 = v.1) (q1 : p1 # u.2 = v.2)
           (p2 : v.1 = w.1) (q2 : p2 # v.2 = w.2)
: path_sigma P u w (p1 @ p2)
             (transport_pp P p1 p2 u.2 @ ap (transport P p2) q1 @ q2)
  = path_sigma P u v p1 q1 @ path_sigma P v w p2 q2.
Proof.
  destruct u, v, w.
simpl in *.
  destruct p1, p2, q1, q2.
  reflexivity.
Defined.
Definition path_sigma_pp_pp' {A : Type} (P : A -> Type)
           {u1 v1 w1 : A} {u2 : P u1} {v2 : P v1} {w2 : P w1}
           (p1 : u1 = v1) (q1 : p1 # u2 = v2)
           (p2 : v1 = w1) (q2 : p2 # v2 = w2)
: path_sigma' P (p1 @ p2)
              (transport_pp P p1 p2 u2 @ ap (transport P p2) q1 @ q2)
  = path_sigma' P p1 q1 @ path_sigma' P p2 q2. exact (@path_sigma_pp_pp A P (u1;u2) (v1;v2) (w1;w2) p1 q1 p2 q2). Defined.

Definition path_sigma_p1_1p' {A : Type} (P : A -> Type)
           {u1 v1 : A} {u2 : P u1} {v2 : P v1}
           (p : u1 = v1) (q : p # u2 = v2)
: path_sigma' P p q
  = path_sigma' P p 1 @ path_sigma' P 1 q.
Proof.
  destruct p, q.
  reflexivity.
Defined.
Definition pr1_path_1 {A : Type} {P : A -> Type} (u : sigT P)
: (idpath u) ..1 = idpath (u .1).
admit.
Defined.
Definition pr1_path_pp {A : Type} {P : A -> Type} {u v w : sigT P}
           (p : u = v) (q : v = w)
: (p @ q) ..1 = (p ..1) @ (q ..1). exact (ap_pp _ _ _). Defined.
Definition pr1_path_V {A : Type} {P : A -> Type} {u v : sigT P} (p : u = v)
: p^ ..1 = (p ..1)^. exact (ap_V _ _). Defined.



Definition ap_existT {A : Type} (P : A -> Type) (x : A) (y1 y2 : P x)
           (q : y1 = y2)
: ap (existT P x) q = path_sigma' P 1 q.
Proof.
  destruct q; reflexivity.
Defined.



Definition transportD_is_transport
           {A:Type} (B:A->Type) (C:sigT B -> Type)
           (x1 x2:A) (p:x1=x2) (y:B x1) (z:C (x1;y))
: transportD B (fun a b => C (a;b)) p y z
  = transport C (path_sigma' B p 1) z.
Proof.
  destruct p.
reflexivity.
Defined.



Definition ap_sigT_rec_path_sigma {A : Type} (P : A -> Type) {Q : Type}
           (x1 x2:A) (p:x1=x2) (y1:P x1) (y2:P x2) (q:p # y1 = y2)
           (d : forall a, P a -> Q)
: ap (sigT_ind (fun _ => Q) d) (path_sigma' P p q)
  = (transport_const p _)^
    @ (ap ((transport (fun _ => Q) p) o (d x1)) (transport_Vp _ p y1))^

    @ (transport_arrow p _ _)^
    @ ap10 (apD d p) (p # y1)
      @ ap (d x2) q.
Proof.
  destruct p.
destruct q.
reflexivity.
Defined.




Definition path_path_sigma_uncurried {A : Type} (P : A -> Type) (u v : sigT P)
           (p q : u = v)
           (rs : {r : p..1 = q..1 & transport (fun x => transport P x u.2 = v.2) r p..2 = q..2})
: p = q.
Proof.
  destruct rs, p, u.
  etransitivity; [ | apply eta_path_sigma ].
  path_induction.
  reflexivity.
Defined.
Definition path_path_sigma {A : Type} (P : A -> Type) (u v : sigT P)
           (p q : u = v)
           (r : p..1 = q..1)
           (s : transport (fun x => transport P x u.2 = v.2) r p..2 = q..2)
: p = q. exact (path_path_sigma_uncurried P u v p q (r; s)). Defined.





Definition transport_sigma {A : Type} {B : A -> Type} {C : forall a:A, B a -> Type}
           {x1 x2 : A} (p : x1 = x2) (yz : { y : B x1 & C x1 y })
: transport (fun x => { y : B x & C x y }) p yz
  = (p # yz.1 ; transportD _ _ p yz.1 yz.2).
admit.
Defined.


Definition transport_sigma' {A B : Type} {C : A -> B -> Type}
           {x1 x2 : A} (p : x1 = x2) (yz : { y : B & C x1 y })
: transport (fun x => { y : B & C x y }) p yz =
  (yz.1 ; transport (fun x => C x yz.1) p yz.2).
admit.
Defined.



Definition transport_sigma_' {A : Type} {B C : A -> Type}
           {D : forall a:A, B a -> C a -> Type}
           {x1 x2 : A} (p : x1 = x2)
           (yzw : { y : B x1 & { z : C x1 & D x1 y z } })
: transport (fun x => { y : B x & { z : C x & D x y z } }) p yzw
  = (p # yzw.1 ; (p # yzw.2.1 ; transportD2 _ _ _ p yzw.1 yzw.2.1 yzw.2.2)).
Proof.
  destruct p.
reflexivity.
Defined.
Definition functor_sigma `{P : A -> Type} `{Q : B -> Type}
           (f : A -> B) (g : forall a, P a -> Q (f a))
: sigT P -> sigT Q. exact (fun u => (f u.1 ; g u.1 u.2)). Defined.

Definition ap_functor_sigma `{P : A -> Type} `{Q : B -> Type}
           (f : A -> B) (g : forall a, P a -> Q (f a))
           (u v : sigT P) (p : u.1 = v.1) (q : p # u.2 = v.2)
: ap (functor_sigma f g) (path_sigma P u v p q)
  = path_sigma Q (functor_sigma f g u) (functor_sigma f g v)
               (ap f p)
               ((transport_compose Q f p (g u.1 u.2))^
                @ (@ap_transport _ P (fun x => Q (f x)) _ _ p g u.2)^
                @ ap (g v.1) q).
Proof.
  destruct u as [u1 u2]; destruct v as [v1 v2]; simpl in p, q.
  destruct p; simpl in q.
  destruct q.
  reflexivity.
Defined.



Global Instance isequiv_functor_sigma `{P : A -> Type} `{Q : B -> Type}
         `{IsEquiv A B f} `{forall a, @IsEquiv (P a) (Q (f a)) (g a)}
: IsEquiv (functor_sigma f g) | 1000.
admit.
Defined.
Definition equiv_functor_sigma `{P : A -> Type} `{Q : B -> Type}
           (f : A -> B) `{IsEquiv A B f}
           (g : forall a, P a -> Q (f a))
           `{forall a, @IsEquiv (P a) (Q (f a)) (g a)}
: sigT P <~> sigT Q. exact (BuildEquiv _ _ (functor_sigma f g) _). Defined.
Definition equiv_functor_sigma' `{P : A -> Type} `{Q : B -> Type}
           (f : A <~> B)
           (g : forall a, P a <~> Q (f a))
: sigT P <~> sigT Q. exact (equiv_functor_sigma f g). Defined.
Definition equiv_functor_sigma_id `{P : A -> Type} `{Q : A -> Type}
           (g : forall a, P a <~> Q a)
: sigT P <~> sigT Q. exact (equiv_functor_sigma (equiv_idmap A) g). Defined.



Global Instance isequiv_pr1_contr {A} {P : A -> Type}
         `{forall a, Contr (P a)}
: IsEquiv (@pr1 A P) | 100.
Proof.
  refine (isequiv_adjointify (@pr1 A P)
                             (fun a => (a ; center (P a))) _ _).
  -
 intros a; reflexivity.
  -
 intros [a p].
    refine (path_sigma' P 1 (contr _)).
Defined.
Definition equiv_sigma_contr {A : Type} (P : A -> Type)
           `{forall a, Contr (P a)}
: sigT P <~> A. exact (BuildEquiv _ _ pr1 _). Defined.



Definition equiv_contr_sigma {A : Type} (P : A -> Type) `{Contr A}
: { x : A & P x } <~> P (center A).
Proof.
  refine (equiv_adjointify (fun xp => (contr xp.1)^ # xp.2)
                           (fun p => (center A ; p)) _ _).
  -
 intros p; simpl.
    exact (ap (fun q => q # p) (path_contr _ 1)).
  -
 intros [a p].
    refine (path_sigma' _ (contr a) _).
    apply transport_pV.
Defined.
Definition equiv_sigma_assoc `(P : A -> Type) (Q : {a : A & P a} -> Type)
: {a : A & {p : P a & Q (a;p)}} <~> sigT Q. exact (@BuildEquiv
       _ _ _
       (@BuildIsEquiv
          {a : A & {p : P a & Q (a;p)}} (sigT Q)
          (fun apq => ((apq.1; apq.2.1); apq.2.2))
          (fun apq => (apq.1.1; (apq.1.2; apq.2)))
          (fun _ => 1)
          (fun _ => 1)
          (fun _ => 1))). Defined.
Definition equiv_sigma_prod `(Q : (A * B) -> Type)
: {a : A & {b : B & Q (a,b)}} <~> sigT Q. exact (@BuildEquiv
       _ _ _
       (@BuildIsEquiv
          {a : A & {b : B & Q (a,b)}} (sigT Q)
          (fun apq => ((apq.1, apq.2.1); apq.2.2))
          (fun apq => (fst apq.1; (snd apq.1; apq.2)))
          (fun _ => 1)
          (fun _ => 1)
          (fun _ => 1))). Defined.
Definition equiv_sigma_symm `(P : A -> B -> Type)
: {a : A & {b : B & P a b}} <~> {b : B & {a : A & P a b}}. exact (equiv_compose'
     (equiv_inverse (equiv_sigma_prod (fun x => P (snd x) (fst x))))
   (equiv_compose'
      (equiv_functor_sigma' (equiv_prod_symm A B)
                            (fun x => equiv_idmap (P (fst x) (snd x))))
      (equiv_sigma_prod (fun x => P (fst x) (snd x))))). Defined.

Definition equiv_sigma_symm0 (A B : Type)
: {a : A & B} <~> {b : B & A}.
Proof.
  refine (BuildEquiv _ _ (fun (w:{a:A & B}) => (w.2 ; w.1)) _).
  refine (BuildIsEquiv _ _ _ (fun (z:{b:B & A}) => (z.2 ; z.1))
                       _ _ _); intros [x y]; reflexivity.
Defined.
Global Instance isequiv_sigT_ind `{P : A -> Type}
         (Q : sigT P -> Type)
: IsEquiv (sigT_ind Q) | 0. exact (BuildIsEquiv
       _ _
       (sigT_ind Q)
       (fun f x y => f (x;y))
       (fun _ => 1)
       (fun _ => 1)
       (fun _ => 1)). Defined.
Definition equiv_sigT_ind `{P : A -> Type}
           (Q : sigT P -> Type)
: (forall (x:A) (y:P x), Q (x;y)) <~> (forall xy, Q xy). exact (BuildEquiv _ _ (sigT_ind Q) _). Defined.
Definition sigT_coind_uncurried
           `{A : X -> Type} (P : forall x, A x -> Type)
: { f : forall x, A x & forall x, P x (f x) }
  -> (forall x, sigT (P x)). exact (fun fg => fun x => (fg.1 x ; fg.2 x)). Defined.
Definition sigT_coind
           `{A : X -> Type} (P : forall x, A x -> Type)
           (f : forall x, A x) (g : forall x, P x (f x))
: (forall x, sigT (P x)). exact (sigT_coind_uncurried P (f;g)). Defined.
Global Instance isequiv_sigT_coind
         `{A : X -> Type} {P : forall x, A x -> Type}
: IsEquiv (sigT_coind_uncurried P) | 0. exact (BuildIsEquiv
       _ _
       (sigT_coind_uncurried P)
       (fun h => existT (fun f => forall x, P x (f x))
                        (fun x => (h x).1)
                        (fun x => (h x).2))
       (fun _ => 1)
       (fun _ => 1)
       (fun _ => 1)). Defined.
Definition equiv_sigT_coind
           `(A : X -> Type) (P : forall x, A x -> Type)
: { f : forall x, A x & forall x, P x (f x) }
    <~> (forall x, sigT (P x)). exact (BuildEquiv _ _ (sigT_coind_uncurried P) _). Defined.



Global Instance trunc_sigma `{P : A -> Type}
         `{IsTrunc n A} `{forall a, IsTrunc n (P a)}
: IsTrunc n (sigT P) | 100.
Proof.
  generalize dependent A.
  induction n; simpl; intros A P ac Pc.
  {
 exists (center A; center (P (center A))).
    intros [a ?].
    refine (path_sigma' P (contr a) (path_contr _ _)).
}
  {
 intros u v.
    refine (trunc_equiv _ (path_sigma_uncurried P u v)).
}
Defined.
Definition path_sigma_hprop {A : Type} {P : A -> Type}
           `{forall x, IsHProp (P x)}
           (u v : sigT P)
: u.1 = v.1 -> u = v. exact (path_sigma_uncurried P u v o pr1^-1). Defined.
Global Instance isequiv_path_sigma_hprop {A P} `{forall x : A, IsHProp (P x)} {u v : sigT P}
: IsEquiv (@path_sigma_hprop A P _ u v) | 100. exact (isequiv_compose). Defined.
Definition equiv_path_sigma_hprop {A : Type} {P : A -> Type}
           {HP : forall a, IsHProp (P a)} (u v : sigT P)
: (u.1 = v.1) <~> (u = v). exact (BuildEquiv _ _ (path_sigma_hprop _ _) _). Defined.

End Sigma.
Import HoTT_DOT_Basics_DOT_Overture.
Import HoTT_DOT_Basics_DOT_Trunc.
Import HoTT_DOT_Basics.
Import HoTT_DOT_Basics_DOT_Trunc.HoTT.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.
Import HoTT_DOT_Basics.HoTT.
Import HoTT_DOT_Basics_DOT_Trunc.HoTT.Basics.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.Basics.

Import HoTT_DOT_Basics.HoTT.Basics.
Local Open Scope equiv_scope.



Ltac issig2 build pr1 pr2 :=

  hnf;

  let fibration := match goal with |- sigT ?fibration <~> ?record => constr:(fibration) end in
  let record := match goal with |- sigT ?fibration <~> ?record => constr:(record) end in
  exact (BuildEquiv _ _ _
                    (BuildIsEquiv
                       (sigT fibration) record
                       (fun u => build u.1 u.2)
                       (fun v => existT fibration (pr1 v) (pr2 v))
                       (fun v => let (v1,v2) as v' return (build (pr1 v') (pr2 v') = v') := v in 1)
                       eta_sigma

                       (fun _ => 1))).


Tactic Notation "issig" constr(build) constr(pr1) constr(pr2) :=
  issig2 build pr1 pr2.



Definition issig_contr (A : Type)
  : { x : A & forall y:A, x = y } <~> Contr A.
Proof.
  issig (BuildContr A) (@center A) (@contr A).
Defined.

Definition issig_equiv (A B : Type)
  : { f : A -> B & IsEquiv f } <~> Equiv A B.
Proof.
  issig (BuildEquiv A B) (@equiv_fun A B) (@equiv_isequiv A B).
Defined.


Ltac issig4 build pr1 pr2 pr3 pr4 :=
  hnf;
  let A := match goal with |- ?A <~> ?B => constr:(A) end in
  let B := match goal with |- ?A <~> ?B => constr:(B) end in
  exact (BuildEquiv _ _ _
                    (BuildIsEquiv
                       A B
                       (fun u => build u.1 u.2.1 u.2.2.1 u.2.2.2)
                       (fun v => (pr1 v; (pr2 v; (pr3 v; pr4 v))))
                       (fun v => let (v1, v2, v3, v4) as v' return (build (pr1 v') (pr2 v') (pr3 v') (pr4 v') = v') := v in 1)
                       eta3_sigma
                       (fun _ => 1))).

Tactic Notation "issig" constr(build) constr(pr1) constr(pr2) constr(pr3) constr(pr4) :=
  issig4 build pr1 pr2 pr3 pr4.



Definition issig_isequiv {A B : Type} (f : A -> B) :
  { g:B->A & { r:Sect g f & { s:Sect f g & forall x : A, r (f x) = ap f (s x) }}}
  <~> IsEquiv f.
Proof.
  issig (BuildIsEquiv A B f) (@equiv_inv A B f) (@eisretr A B f)
        (@eissect A B f) (@eisadj A B f).
Defined.
Module Export Equiv.
Import HoTT_DOT_Basics_DOT_Overture.
Import HoTT_DOT_Basics_DOT_Trunc.
Import HoTT_DOT_Basics.
Import HoTT_DOT_Basics_DOT_Trunc.HoTT.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.
Import HoTT_DOT_Basics.HoTT.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.Basics.
Import HoTT_DOT_Basics.HoTT.Basics.



Section AssumeFunext.
  Context `{Funext}.



  Global Instance hprop_isequiv {A B} `(f : A -> B)
  : IsHProp (IsEquiv f).
admit.
Defined.


  Lemma equiv_path_equiv {A B : Type} (e1 e2 : A <~> B)
  : (e1 = e2 :> (A -> B)) <~> (e1 = e2 :> (A <~> B)).
admit.
Defined.
Definition path_equiv {A B : Type} {e1 e2 : A <~> B}
  : (e1 = e2 :> (A -> B)) -> (e1 = e2 :> (A <~> B)).
admit.
Defined.


  Global Instance istrunc_equiv {n : trunc_index} {A B : Type} `{IsTrunc n.+1 B}
  : IsTrunc n.+1 (A <~> B).
  Proof.
    simpl.
intros e1 e2.
    apply (trunc_equiv _ (equiv_path_equiv e1 e2)).
  Defined.


  Global Instance contr_equiv_contr_contr {A B : Type} `{Contr A} `{Contr B}
  : Contr (A <~> B).
admit.
Defined.
Definition functor_equiv {A B C D} (h : A <~> C) (k : B <~> D)
  : (A <~> B) -> (C <~> D).
admit.
Defined.

  Global Instance isequiv_functor_equiv {A B C D} (h : A <~> C) (k : B <~> D)
  : IsEquiv (functor_equiv h k).
admit.
Defined.
Definition equiv_functor_equiv {A B C D} (h : A <~> C) (k : B <~> D)
  : (A <~> B) <~> (C <~> D).
admit.
Defined.

End AssumeFunext.

End Equiv.
Import HoTT_DOT_Basics_DOT_Overture.
Import HoTT_DOT_Basics_DOT_Trunc.
Import HoTT_DOT_Basics.
Import HoTT_DOT_Basics_DOT_Trunc.HoTT.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.
Import HoTT_DOT_Basics.HoTT.
Import HoTT_DOT_Basics_DOT_Trunc.HoTT.Basics.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.Basics.


Local Unset Elimination Schemes.
Inductive Bool : Type1 :=
  | true : Bool
  | false : Bool.
Scheme Bool_ind := Induction for Bool Sort Type.
Definition andb (b1 b2 : Bool) : Bool.
admit.
Defined.
Definition orb (b1 b2 : Bool) : Bool.
admit.
Defined.
Global Instance trunc_if n A B `{IsTrunc n A, IsTrunc n B} (b : Bool)
: IsTrunc n (if b then A else B) | 100.
admit.
Defined.

Section BoolDecidable.
Definition false_ne_true : ~false = true. exact (fun H => match H in (_ = y) return (if y then Empty else Bool) with
                  | 1%path => true
                end). Defined.
Definition true_ne_false : ~true = false. exact (fun H => false_ne_true (symmetry _ _ H)). Defined.
Global Instance decidable_paths_bool : DecidablePaths Bool. exact (fun x y => match x as x, y as y return ((x = y) + (~x = y)) with
                    | true, true => inl idpath
                    | false, false => inl idpath
                    | true, false => inr true_ne_false
                    | false, true => inr false_ne_true
                  end). Defined.
End BoolDecidable.

Section BoolForall.
End BoolForall.

Section EquivBoolEquiv.

End EquivBoolEquiv.

Lemma Empty_rec {T : Type} (falso: Empty) : T.
admit.
Defined.

Global Instance all_to_empty_isequiv (T : Type) (f : T -> Empty) : IsEquiv f.
admit.
Defined.
Import HoTT_DOT_Basics_DOT_Overture.
Import HoTT_DOT_Basics_DOT_Trunc.
Import HoTT_DOT_Basics.
Import HoTT_DOT_Basics_DOT_Trunc.HoTT.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.
Import HoTT_DOT_Basics.HoTT.
Import HoTT_DOT_Basics_DOT_Trunc.HoTT.Basics.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.Basics.

Import HoTT_DOT_Basics.HoTT.Basics.

Scheme nat_ind := Induction for nat Sort Type.
Scheme nat_rec := Minimality for nat Sort Type.
Module Export Sum.
Import HoTT_DOT_Basics_DOT_Overture.
Import HoTT_DOT_Basics_DOT_Trunc.
Import HoTT_DOT_Basics.
Import HoTT_DOT_Basics_DOT_Trunc.HoTT.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.
Import HoTT_DOT_Basics.HoTT.
Import HoTT_DOT_Basics_DOT_Trunc.HoTT.Basics.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.Basics.

Import HoTT_DOT_Basics.HoTT.Basics.
Local Open Scope trunc_scope.
Generalizable Variables X A B f g n.

Scheme sum_ind := Induction for sum Sort Type.







Definition eta_sum `(z : A + B) : match z with
                                    | inl z' => inl z'
                                    | inr z' => inr z'
                                  end = z
  := match z with inl _ => 1 | inr _ => 1 end.



Definition path_sum {A B : Type} (z z' : A + B)
           (pq : match z, z' with
                   | inl z0, inl z'0 => z0 = z'0
                   | inr z0, inr z'0 => z0 = z'0
                   | _, _ => Empty
                 end)
: z = z'.
  destruct z, z', pq; exact idpath.
Defined.

Definition path_sum_inv {A B : Type} {z z' : A + B}
           (pq : z = z')
: match z, z' with
    | inl z0, inl z'0 => z0 = z'0
    | inr z0, inr z'0 => z0 = z'0
    | _, _ => Empty
  end
  := match pq with
       | 1 => match z with
                | inl _ => 1
                | inr _ => 1
              end
     end.


Definition path_sum_inl {A B : Type} {x x' : A}
: inl x = inl x' -> x = x'
  := fun p => @path_sum_inv A B _ _ p.

Definition path_sum_inr {A B : Type} {x x' : B}
: inr x = inr x' -> x = x'
  := fun p => @path_sum_inv A B _ _ p.
Definition eisretr_path_sum {A B} {z z' : A + B}
: Sect (@path_sum_inv _ _ z z') (path_sum z z'). exact (fun p => match p as p in (_ = z') return
                    path_sum z z' (path_sum_inv p) = p
              with
                | 1 => match z as z return
                             path_sum z z (path_sum_inv 1) = 1
                       with
                         | inl _ => 1
                         | inr _ => 1
                       end
              end). Defined.

Definition eissect_path_sum {A B} {z z' : A + B}
: Sect (path_sum z z') (@path_sum_inv _ _ z z').
Proof.
  intro p.
  destruct z, z', p; exact idpath.
Defined.

Global Instance isequiv_path_sum {A B : Type} {z z' : A + B}
: IsEquiv (path_sum z z') | 0.
Proof.
  refine (BuildIsEquiv _ _
                       (path_sum z z')
                       (@path_sum_inv _ _ z z')
                       (@eisretr_path_sum A B z z')
                       (@eissect_path_sum A B z z')
                       _).
  destruct z, z';
    intros [];
    exact idpath.
Defined.

Definition equiv_path_sum {A B : Type} (z z' : A + B)
  := BuildEquiv _ _ _ (@isequiv_path_sum A B z z').



Definition transport_sum {A : Type} {P Q : A -> Type} {a a' : A} (p : a = a')
           (z : P a + Q a)
: transport (fun a => P a + Q a) p z = match z with
                                         | inl z' => inl (p # z')
                                         | inr z' => inr (p # z')
                                       end
  := match p with idpath => match z with inl _ => 1 | inr _ => 1 end end.
Definition functor_sum {A A' B B' : Type} (f : A -> A') (g : B -> B')
: A + B -> A' + B'. exact (fun z => match z with inl z' => inl (f z') | inr z' => inr (g z') end). Defined.



Global Instance isequiv_functor_sum `{IsEquiv A A' f} `{IsEquiv B B' g}
: IsEquiv (functor_sum f g) | 1000.
Proof.
  apply (isequiv_adjointify
           (functor_sum f g)
           (functor_sum f^-1 g^-1));
  [ intros [?|?]; simpl; apply ap; apply eisretr
  | intros [?|?]; simpl; apply ap; apply eissect ].
Defined.
Definition equiv_functor_sum `{IsEquiv A A' f} `{IsEquiv B B' g}
: A + B <~> A' + B'. exact (BuildEquiv _ _ (functor_sum f g) _). Defined.
Definition equiv_functor_sum' {A A' B B' : Type} (f : A <~> A') (g : B <~> B')
: A + B <~> A' + B'. exact (equiv_functor_sum (f := f) (g := g)). Defined.
Definition equiv_functor_sum_l {A B B' : Type} (g : B <~> B')
: A + B <~> A + B'. exact (equiv_functor_sum (f := idmap) (g := g)). Defined.
Definition equiv_functor_sum_r {A A' B : Type} (f : A <~> A')
: A + B <~> A' + B. exact (equiv_functor_sum (f := f) (g := idmap)). Defined.





Definition equiv_sum_symm (A B : Type) : A + B <~> B + A.
Proof.
  apply (equiv_adjointify
           (fun ab => match ab with inl a => inr a | inr b => inl b end)
           (fun ab => match ab with inl a => inr a | inr b => inl b end));
  intros [?|?]; exact idpath.
Defined.
Definition sum_ind_uncurried {A B} (P : A + B -> Type)
           (fg : (forall a, P (inl a)) * (forall b, P (inr b)))
: forall s, P s. exact (@sum_ind A B P (fst fg) (snd fg)). Defined.


Global Instance isequiv_sum_ind `{Funext} `(P : A + B -> Type)
: IsEquiv (sum_ind_uncurried P) | 0.
Proof.
  apply (isequiv_adjointify
           (sum_ind_uncurried P)
           (fun f => (fun a => f (inl a), fun b => f (inr b))));
  repeat ((exact idpath)
            || intros []
            || intro
            || apply path_forall).
Defined.

Definition equiv_sum_ind `{Funext} `(P : A + B -> Type)
  := BuildEquiv _ _ _ (isequiv_sum_ind P).
Definition equiv_sum_distributive `{Funext} (A B C : Type)
: (A -> C) * (B -> C) <~> (A + B -> C). exact (equiv_sum_ind (fun _ => C)). Defined.



Global Instance trunc_sum n' (n := n'.+2)
         `{IsTrunc n A, IsTrunc n B}
: IsTrunc n (A + B) | 100.
Proof.
  intros a b.
  eapply trunc_equiv';
    [ exact (equiv_path_sum _ _) | ].
  destruct a, b; simpl in *;
  try typeclasses eauto;
  intros [].
Defined.
Global Instance hset_sum `{HA : IsHSet A, HB : IsHSet B} : IsHSet (A + B) | 100.
admit.
Defined.
Definition sigT_of_sum A B (x : A + B)
: { b : Bool & if b then A else B }. exact ((_;
      match
        x as s
        return
        (if match s with
              | inl _ => true
              | inr _ => false
            end then A else B)
      with
        | inl a => a
        | inr b => b
      end)). Defined.
Definition sum_of_sigT A B (x : { b : Bool & if b then A else B })
: A + B. exact (match x with
       | (true; a) => inl a
       | (false; b) => inr b
     end). Defined.

Global Instance isequiv_sigT_of_sum A B : IsEquiv (@sigT_of_sum A B) | 0.
Proof.
  apply (isequiv_adjointify (@sigT_of_sum A B)
                            (@sum_of_sigT A B));
  repeat (intros [] || intro); exact idpath.
Defined.
Global Instance isequiv_sum_of_sigT A B : IsEquiv (sum_of_sigT A B). exact (isequiv_inverse (@sigT_of_sum A B)). Defined.


Definition trunc_sum' n A B `{IsTrunc n Bool, IsTrunc n A, IsTrunc n B}
: (IsTrunc n (A + B)).
Proof.
  eapply trunc_equiv'; [ esplit;
                         exact (@isequiv_sum_of_sigT _ _)
                       | ].
  typeclasses eauto.
Defined.

End Sum.
Module Export Universe.
Import HoTT_DOT_Basics_DOT_Overture.
Import HoTT_DOT_Basics_DOT_Trunc.
Import HoTT_DOT_Basics.
Import HoTT_DOT_Basics_DOT_Trunc.HoTT.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.
Import HoTT_DOT_Basics.HoTT.
Import HoTT_DOT_Basics_DOT_Trunc.HoTT.Basics.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.Basics.

Import HoTT_DOT_Basics.HoTT.Basics.

Generalizable Variables A B f.
Global Instance isequiv_path {A B : Type} (p : A = B)
  : IsEquiv (transport (fun X:Type => X) p) | 0. exact (BuildIsEquiv _ _ _ (transport (fun X:Type => X) p^)
  (transport_pV idmap p)
  (transport_Vp idmap p)
  (fun a => match p in _ = C return
              (transport_pp idmap p^ p (transport idmap p a))^ @
                 transport2 idmap (concat_Vp p) (transport idmap p a) =
              ap (transport idmap p) ((transport_pp idmap p p^ a) ^ @
                transport2 idmap (concat_pV p) a) with idpath => 1 end)). Defined.
Definition equiv_path (A B : Type) (p : A = B) : A <~> B. exact (BuildEquiv _ _ (transport (fun X:Type => X) p) _). Defined.

Definition equiv_path_V `{Funext} (A B : Type) (p : A = B) :
  equiv_path B A (p^) = equiv_inverse (equiv_path A B p).
admit.
Defined.


Class Univalence.
Axiom isequiv_equiv_path : forall `{Univalence} (A B : Type), IsEquiv (equiv_path A B).

Section Univalence.
Context `{Univalence}.
Definition path_universe_uncurried {A B : Type} (f : A <~> B) : A = B. exact ((equiv_path A B)^-1 f). Defined.
Definition path_universe {A B : Type} (f : A -> B) {feq : IsEquiv f} : (A = B). exact (path_universe_uncurried (BuildEquiv _ _ f feq)). Defined.
Definition eta_path_universe {A B : Type} (p : A = B)
  : path_universe (equiv_path A B p) = p. exact (eissect (equiv_path A B) p). Defined.
Definition isequiv_path_universe {A B : Type}
  : IsEquiv (@path_universe_uncurried A B). exact (_). Defined.
Definition equiv_path_universe (A B : Type) : (A <~> B) <~> (A = B). exact (BuildEquiv _ _ (@path_universe_uncurried A B) isequiv_path_universe). Defined.

Definition path_universe_V_uncurried `{Funext} {A B : Type} (f : A <~> B)
  : path_universe_uncurried (equiv_inverse f) = (path_universe_uncurried f)^.
Proof.
  revert f.
equiv_intro ((equiv_path_universe A B)^-1) p.
simpl.
  transitivity (p^).
    2: exact (inverse2 (eisretr (equiv_path_universe A B) p)^).
  unfold compose.
transitivity (path_universe_uncurried (equiv_path B A p^)).
    by refine (ap _ (equiv_path_V A B p)^).
  by refine (eissect (equiv_path B A) p^).
Defined.
Definition path_universe_V `{Funext} `(f : A -> B) `{IsEquiv A B f}
  : path_universe (f^-1) = (path_universe f)^. exact (path_universe_V_uncurried (BuildEquiv A B f _)). Defined.




Definition transport_path_universe_uncurried
           {A B : Type} (f : A <~> B) (z : A)
  : transport (fun X:Type => X) (path_universe f) z = f z.
Proof.
  revert f.
 equiv_intro (equiv_path A B) p.
  exact (ap (fun s => transport idmap s z) (eissect _ p)).
Defined.
Definition transport_path_universe
           {A B : Type} (f : A -> B) {feq : IsEquiv f} (z : A)
  : transport (fun X:Type => X) (path_universe f) z = f z. exact (transport_path_universe_uncurried (BuildEquiv A B f feq) z). Defined.
Definition transport_path_universe_equiv_path
           {A B : Type} (p : A = B) (z : A)
  : transport_path_universe (equiv_path A B p) z =
    (ap (fun s => transport idmap s z) (eissect _ p)). exact (equiv_ind_comp _ _ _). Defined.
Definition transport_path_universe'
  {A : Type} (P : A -> Type) {x y : A} (p : x = y)
  (f : P x <~> P y) (q : ap P p = path_universe f) (u : P x)
  : transport P p u = f u. exact (transport_compose idmap P p u
   @ ap10 (ap (transport idmap) q) u
   @ transport_path_universe f u). Defined.



Definition transport_path_universe_V_uncurried `{Funext}
           {A B : Type} (f : A <~> B) (z : B)
  : transport (fun X:Type => X) (path_universe f)^ z = f^-1 z.
Proof.
  revert f.
equiv_intro (equiv_path A B) p.
  exact (ap (fun s => transport idmap s z) (inverse2 (eissect _ p))).
Defined.
Definition transport_path_universe_V `{Funext}
           {A B : Type} (f : A -> B) {feq : IsEquiv f} (z : B)
  : transport (fun X:Type => X) (path_universe f)^ z = f^-1 z. exact (transport_path_universe_V_uncurried (BuildEquiv _ _ f feq) z). Defined.
Definition transport_path_universe_V_equiv_path `{Funext}
           {A B : Type} (p : A = B) (z : B)
  : transport_path_universe_V (equiv_path A B p) z =
    ap (fun s => transport idmap s z) (inverse2 (eissect _ p)). exact (equiv_ind_comp _ _ _). Defined.



Definition transport_path_universe_Vp_uncurried `{Funext}
           {A B : Type} (f : A <~> B) (z : A)
: ap (transport idmap (path_universe f)^) (transport_path_universe f z)
  @ transport_path_universe_V f (f z)
  @ eissect f z
  = transport_Vp idmap (path_universe f) z.
Proof.
  pattern f.
  refine (equiv_ind (equiv_path A B) _ _ _); intros p.

  refine (_ @ ap_transport_Vp p (path_universe (equiv_path A B p))
            (eissect (equiv_path A B) p) z).
  apply whiskerR.
apply concat2.
  -
 apply ap.
apply transport_path_universe_equiv_path.
  -
 apply transport_path_universe_V_equiv_path.
Defined.
Definition transport_path_universe_Vp `{Funext}
           {A B : Type} (f : A -> B) {feq : IsEquiv f} (z : A)
: ap (transport idmap (path_universe f)^) (transport_path_universe f z)
  @ transport_path_universe_V f (f z)
  @ eissect f z
  = transport_Vp idmap (path_universe f) z. exact (transport_path_universe_Vp_uncurried (BuildEquiv A B f feq) z). Defined.




Theorem equiv_induction {U : Type} (P : forall V, U <~> V -> Type) :
  (P U (equiv_idmap U)) -> (forall V (w : U <~> V), P V w).
Proof.
  intros H0 V w.
  apply (equiv_ind (equiv_path U V)).
  exact (paths_ind U (fun Y p => P Y (equiv_path U Y p)) H0 V).
Defined.
Definition equiv_induction_comp {U : Type} (P : forall V, U <~> V -> Type)
  (didmap : P U (equiv_idmap U))
  : equiv_induction P didmap U (equiv_idmap U) = didmap. exact ((equiv_ind_comp (P U) _ 1)). Defined.


Theorem equiv_induction' (P : forall U V, U <~> V -> Type) :
  (forall T, P T T (equiv_idmap T)) -> (forall U V (w : U <~> V), P U V w).
Proof.
  intros H0 U V w.
  apply (equiv_ind (equiv_path U V)).
  exact (paths_ind' (fun X Y p => P X Y (equiv_path X Y p)) H0 U V).
Defined.
Definition equiv_induction'_comp (P : forall U V, U <~> V -> Type)
  (didmap : forall T, P T T (equiv_idmap T)) (U : Type)
  : equiv_induction' P didmap U U (equiv_idmap U) = didmap U. exact ((equiv_ind_comp (P U U) _ 1)). Defined.

End Univalence.

End Universe.
Import HoTT_DOT_Basics_DOT_Overture.
Import HoTT_DOT_Basics_DOT_Trunc.
Import HoTT_DOT_Basics.
Import HoTT_DOT_Basics_DOT_Trunc.HoTT.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.
Import HoTT_DOT_Basics.HoTT.
Import HoTT_DOT_Basics_DOT_Trunc.HoTT.Basics.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.Basics.
Import HoTT_DOT_Basics_DOT_Overture.
Import HoTT_DOT_Basics_DOT_Trunc.
Import HoTT_DOT_Basics.
Import HoTT_DOT_Basics_DOT_Trunc.HoTT.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.
Import HoTT_DOT_Basics.HoTT.
Import HoTT_DOT_Basics_DOT_Trunc.HoTT.Basics.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.Basics.
Import HoTT_DOT_Basics.HoTT.Basics.




Global Instance contr_contr `{Funext} (A : Type)
  : Contr A -> Contr (Contr A) | 100.
admit.
Defined.


Global Instance hprop_trunc `{Funext} (n : trunc_index) (A : Type)
  : IsHProp (IsTrunc n A) | 0.
admit.
Defined.



Global Instance isprop_istruncmap `{Funext} (n : trunc_index) {X Y : Type} (f : X -> Y)
: IsHProp (IsTruncMap n f).
Proof.
  unfold IsTruncMap.
  exact _.
Defined.



Theorem equiv_hprop_allpath `{Funext} (A : Type)
  : IsHProp A <~> (forall (x y : A), x = y).
admit.
Defined.

Theorem equiv_hprop_inhabited_contr `{Funext} {A}
  : IsHProp A <~> (A -> Contr A).
admit.
Defined.



Theorem equiv_contr_inhabited_hprop `{Funext} {A}
  : Contr A <~> A * IsHProp A.
Proof.
  assert (f : Contr A -> A * IsHProp A).
    intro P.
split.
exact (@center _ P).
apply @trunc_succ.
exact P.
  assert (g : A * IsHProp A -> Contr A).
    intros [a P].
apply (@contr_inhabited_hprop _ P a).
  refine (@equiv_iff_hprop _ _ _ _ f g).
  apply hprop_inhabited_contr; intro p.
  apply @contr_prod.
  exact (g p).
apply (@contr_inhabited_hprop _ _ (snd p)).
Defined.

Theorem equiv_contr_inhabited_allpath `{Funext} {A}
  : Contr A <~> A * forall (x y : A), x = y.
admit.
Defined.




Global Instance isequiv_equiv_iff_hprop_uncurried
       `{Funext} {A B} `{IsHProp A} `{IsHProp B}
: IsEquiv (@equiv_iff_hprop_uncurried A _ B _) | 0.
admit.
Defined.




Lemma if_hprop_then_equiv_Unit (hprop : Type) `{IsHProp hprop} :  hprop -> hprop <~> Unit.
admit.
Defined.


Lemma if_not_hprop_then_equiv_Empty (hprop : Type) `{IsHProp hprop} : ~hprop -> hprop <~> Empty.
admit.
Defined.
Import HoTT_DOT_Basics_DOT_Overture.
Import HoTT_DOT_Basics_DOT_Trunc.
Import HoTT_DOT_Basics.
Import HoTT_DOT_Basics_DOT_Trunc.HoTT.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.
Import HoTT_DOT_Basics.HoTT.
Import HoTT_DOT_Basics_DOT_Trunc.HoTT.Basics.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.Basics.

Import HoTT_DOT_Basics_DOT_Overture.HoTT.Basics.Overture.
Import HoTT_DOT_Basics_DOT_Overture.
Import HoTT_DOT_Basics_DOT_Trunc.
Import HoTT_DOT_Basics.
Import HoTT_DOT_Basics_DOT_Trunc.HoTT.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.
Import HoTT_DOT_Basics.HoTT.
Import HoTT_DOT_Basics_DOT_Trunc.HoTT.Basics.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.Basics.
Import HoTT_DOT_Basics.HoTT.Basics.


Lemma path_forall_1_beta `{Funext} A B x P f g e Px
: @transport (forall a : A, B a) (fun f => P (f x)) f g (@path_forall _ _ _ _ _ e) Px
  = @transport (B x) P (f x) (g x) (e x) Px.
admit.
Defined.


Lemma path_forall_recr_beta' `{Funext} A B x0 P f g e Px
: @transport (forall a : A, B a)
             (fun f => P f (f x0))
             f
             g
             (@path_forall _ _ _ _ _ e)
             Px
  = @transport ((forall a, B a) * B x0)%type
               (fun x => P (fst x) (snd x))
               (f, f x0)
               (g, g x0)
               (path_prod' (@path_forall _ _ _ _ _ e) (e x0))
               Px.
admit.
Defined.


Lemma path_forall_recr_beta `{Funext} A B x0 P f g e Px
: @transport (forall a : A, B a)
             (fun f => P f (f x0))
             f
             g
             (@path_forall _ _ _ _ _ e)
             Px
  = @transport (forall x : A, B x)
               (fun x => P x (g x0))
               f
               g
               (@path_forall H A B f g e)
               (@transport (B x0)
                           (fun y => P f y)
                           (f x0)
                           (g x0)
                           (e x0)
                           Px).
admit.
Defined.


Lemma path_forall_2_beta' `{Funext} A B x0 x1 P f g e Px
: @transport (forall a : A, B a) (fun f => P (f x0) (f x1)) f g (@path_forall _ _ _ _ _ e) Px
  = @transport (B x0 * B x1)%type (fun x => P (fst x) (snd x)) (f x0, f x1) (g x0, g x1) (path_prod' (e x0) (e x1)) Px.
admit.
Defined.

Lemma path_forall_2_beta `{Funext} A B x0 x1 P f g e Px
: @transport (forall a : A, B a) (fun f => P (f x0) (f x1)) f g (@path_forall _ _ _ _ _ e) Px
  = transport (fun y : B x1 => P (g x0) y) (e x1)
     (transport (fun y : B x0 => P y (f x1)) (e x0) Px).
admit.
Defined.


Definition match_eta {T} {x y : T} (H0 : x = y)
: (H0 = match H0 in (_ = y) return (x = y) with
          | idpath => idpath
        end)
  := match H0 with idpath => idpath end.
Definition match_eta1 {T} {x : T} (E : x = x)
: (match E in (_ = y) return (x = y) with
     | idpath => idpath
   end = idpath)
  -> idpath = E. exact (fun H => ((H # match_eta E) ^)%path). Defined.
Definition match_eta2 {T} {x : T} (E : x = x)
: (idpath
   = match E in (_ = y) return (x = y) with
       | idpath => idpath
     end)
  -> idpath = E.
admit.
Defined.
Import HoTT_DOT_Basics_DOT_Overture.
Import HoTT_DOT_Basics_DOT_Trunc.
Import HoTT_DOT_Basics.
Import HoTT_DOT_Basics_DOT_Trunc.HoTT.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.
Import HoTT_DOT_Basics.HoTT.
Import HoTT_DOT_Basics_DOT_Trunc.HoTT.Basics.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.Basics.
Import HoTT_DOT_Basics.HoTT.Basics.

Generalizable Variables A B f.

Section AssumeFunext.







Definition fcontr_isequiv `(f : A -> B)
  : IsEquiv f -> (forall b:B, Contr {a : A & f a = b}).
admit.
Defined.

Definition isequiv_fcontr `(f : A -> B)
  : (forall b:B, Contr {a : A & f a = b}) -> IsEquiv f.
admit.
Defined.



Definition contr_sect_equiv `(f : A -> B) `{IsEquiv A B f}
  : Contr {g : B -> A & Sect g f}.
admit.
Defined.

Definition contr_retr_equiv `(f : A -> B) `{IsEquiv A B f}
  : Contr {g : B -> A & Sect f g}.
admit.
Defined.



Local Instance hprop_isequiv `(f : A -> B) : IsHProp (IsEquiv f).
admit.
Defined.



Definition equiv_fcontr_isequiv `(f : A -> B)
  : (forall b:B, Contr {a : A & f a = b}) <~> IsEquiv f.
admit.
Defined.



Local Definition equiv_fcontr_isequiv' `(f : A -> B)
  : (forall b:B, Contr {a : A & f a = b}) <~> IsEquiv f.
admit.
Defined.
Definition BiInv `(f : A -> B) : Type. exact ({g : B -> A & Sect f g} * {h : B -> A & Sect h f}). Defined.



Definition isequiv_biinv `(f : A -> B)
  : BiInv f -> IsEquiv f.
admit.
Defined.

Global Instance isprop_biinv `(f : A -> B) : IsHProp (BiInv f) | 0.
admit.
Defined.

Definition equiv_biinv_isequiv `(f : A -> B)
  : BiInv f <~> IsEquiv f.
admit.
Defined.



Fixpoint PathSplit (n : nat) `(f : A -> B) : Type
  := match n with
       | 0 => Unit
       | S n => (forall a, hfiber f a) *
                forall (x y : A), PathSplit n (@ap _ _ f x y)
     end.

Definition isequiv_pathsplit (n : nat) `{f : A -> B}
: PathSplit n.+2 f -> IsEquiv f.
admit.
Defined.

Global Instance contr_pathsplit_isequiv
           (n : nat) `(f : A -> B) `{IsEquiv _ _ f}
: Contr (PathSplit n f).
admit.
Defined.

Global Instance ishprop_pathsplit (n : nat) `(f : A -> B)
: IsHProp (PathSplit n.+2 f).
admit.
Defined.

Definition equiv_pathsplit_isequiv (n : nat) `(f : A -> B)
: PathSplit n.+2 f <~> IsEquiv f.
admit.
Defined.


Lemma equiv_functor_pathsplit (n : nat) {A B C D}
      (f : A -> B) (g : C -> D) (h : A <~> C) (k : B <~> D)
      (p : g o h == k o f)
: PathSplit n f <~> PathSplit n g.
admit.
Defined.
Definition ooPathSplit `(f : A -> B) : Type. exact (forall n, PathSplit n f). Defined.
Definition isequiv_oopathsplit `{f : A -> B}
: ooPathSplit f -> IsEquiv f. exact (fun ps => isequiv_pathsplit 0 (ps 2)). Defined.

Global Instance contr_oopathsplit_isequiv
           `(f : A -> B) `{IsEquiv _ _ f}
: Contr (ooPathSplit f).
admit.
Defined.

Global Instance ishprop_oopathsplit `(f : A -> B)
: IsHProp (ooPathSplit f).
admit.
Defined.

Definition equiv_oopathsplit_isequiv `(f : A -> B)
: ooPathSplit f <~> IsEquiv f.
admit.
Defined.

End AssumeFunext.
Import HoTT_DOT_Basics_DOT_Overture.
Import HoTT_DOT_Basics_DOT_Trunc.
Import HoTT_DOT_Basics.
Import HoTT_DOT_Basics_DOT_Overture.HoTT.
Import HoTT_DOT_Basics.HoTT.




  Definition ExtensionAlong {A B : Type} (f : A -> B)
             (P : B -> Type) (d : forall x:A, P (f x))
    := { s : forall y:B, P y & forall x:A, s (f x) = d x }.

  Definition path_extension {A B : Type} {f : A -> B}
             {P : B -> Type} {d : forall x:A, P (f x)}
             (ext ext' : ExtensionAlong f P d)
  : (ExtensionAlong f
                    (fun y => pr1 ext y = pr1 ext' y)
                    (fun x => pr2 ext x @ (pr2 ext' x)^))
    -> ext = ext'.
admit.
Defined.

  Global Instance isequiv_path_extension {A B : Type} {f : A -> B}
         {P : B -> Type} {d : forall x:A, P (f x)}
         (ext ext' : ExtensionAlong f P d)
  : IsEquiv (path_extension ext ext') | 0.
admit.
Defined.




  Fixpoint ExtendableAlong
           (n : nat) {A B : Type} (f : A -> B) (C : B -> Type) : Type
    := match n with
         | 0 => Unit
         | S n => (forall (g : forall a, C (f a)), ExtensionAlong f C g) *
                  forall (h k : forall b, C b),
                    ExtendableAlong n f (fun b => h b = k b)
       end.

  Definition equiv_extendable_pathsplit (n : nat)
             {A B : Type} (C : B -> Type) (f : A -> B)
  : ExtendableAlong n f C
                    <~> PathSplit n (fun (g : forall b, C b) => g oD f).
admit.
Defined.

  Definition isequiv_extendable (n : nat)
             {A B : Type} {C : B -> Type} {f : A -> B}
  : ExtendableAlong n.+2 f C
    -> IsEquiv (fun g => g oD f)
    := isequiv_pathsplit n o (equiv_extendable_pathsplit n.+2 C f).

  Global Instance ishprop_extendable (n : nat)
         {A B : Type} (C : B -> Type) (f : A -> B)
  : IsHProp (ExtendableAlong n.+2 f C).
admit.
Defined.

  Definition equiv_extendable_isequiv (n : nat)
             {A B : Type} (C : B -> Type) (f : A -> B)
  : ExtendableAlong n.+2 f C
                    <~> IsEquiv (fun (g : forall b, C b) => g oD f).
admit.
Defined.


  Definition extendable_postcompose' (n : nat)
             {A B : Type} (C D : B -> Type) (f : A -> B)
             (g : forall b, C b <~> D b)
  : ExtendableAlong n f C -> ExtendableAlong n f D.
admit.
Defined.
Definition extendable_postcompose (n : nat)
             {A B : Type} (C D : B -> Type) (f : A -> B)
             (g : forall b, C b -> D b) `{forall b, IsEquiv (g b)}
  : ExtendableAlong n f C -> ExtendableAlong n f D. exact (extendable_postcompose' n C D f (fun b => BuildEquiv _ _ (g b) _)). Defined.


  Definition extendable_compose (n : nat)
             {A B C : Type} (P : C -> Type) (f : A -> B) (g : B -> C)
  : ExtendableAlong n g P -> ExtendableAlong n f (P o g) -> ExtendableAlong n (g o f) P.
admit.
Defined.


  Definition cancelL_extendable (n : nat)
             {A B C : Type} (P : C -> Type) (f : A -> B) (g : B -> C)
  : ExtendableAlong n g P -> ExtendableAlong n (g o f) P -> ExtendableAlong n f (P o g).
admit.
Defined.

  Definition cancelR_extendable (n : nat)
             {A B C : Type} (P : C -> Type) (f : A -> B) (g : B -> C)
  : ExtendableAlong n.+1 f (P o g) -> ExtendableAlong n (g o f) P -> ExtendableAlong n g P.
admit.
Defined.


  Definition extendable_homotopic (n : nat)
             {A B : Type} (C : B -> Type) (f : A -> B) {g : A -> B} (p : f == g)
  : ExtendableAlong n f C -> ExtendableAlong n g C.
admit.
Defined.


  Definition extendable_equiv (n : nat)
             {A B : Type} (C : B -> Type) (f : A -> B) `{IsEquiv _ _ f}
  : ExtendableAlong n f C.
admit.
Defined.


  Definition extendable_contr (n : nat)
             {A B : Type} (C : B -> Type) (f : A -> B)
             `{forall b, Contr (C b)}
  : ExtendableAlong n f C.
admit.
Defined.


  Definition extendable_homotopy (n : nat)
             {A B : Type} (C : B -> Type) (f : A -> B)
             (h k : forall b, C b)
  : ExtendableAlong n.+1 f C -> ExtendableAlong n f (fun b => h b = k b).
admit.
Defined.
Definition ooExtendableAlong
             {A B : Type} (f : A -> B) (C : B -> Type) : Type. exact (forall n, ExtendableAlong n f C). Defined.

  Definition isequiv_ooextendable
             {A B : Type} (C : B -> Type) (f : A -> B)
  : ooExtendableAlong f C -> IsEquiv (fun g => g oD f)
    := fun ps => isequiv_extendable 0 (ps 2).

  Definition equiv_ooextendable_pathsplit
             {A B : Type} (C : B -> Type) (f : A -> B)
  : ooExtendableAlong f C <~>
                      ooPathSplit (fun (g : forall b, C b) => g oD f).
admit.
Defined.

  Global Instance ishprop_ooextendable
         {A B : Type} (C : B -> Type) (f : A -> B)
  : IsHProp (ooExtendableAlong f C).
admit.
Defined.

  Definition equiv_ooextendable_isequiv
             {A B : Type} (C : B -> Type) (f : A -> B)
  : ooExtendableAlong f C
                      <~> IsEquiv (fun (g : forall b, C b) => g oD f).
admit.
Defined.
Definition ooextendable_postcompose
             {A B : Type} (C D : B -> Type) (f : A -> B)
             (g : forall b, C b -> D b) `{forall b, IsEquiv (g b)}
  : ooExtendableAlong f C -> ooExtendableAlong f D. exact (fun ppp n => extendable_postcompose n C D f g (ppp n)). Defined.
Definition ooextendable_compose
             {A B C : Type} (P : C -> Type) (f : A -> B) (g : B -> C)
  : ooExtendableAlong g P -> ooExtendableAlong f (P o g) -> ooExtendableAlong (g o f) P. exact (fun extg extf n => extendable_compose n P f g (extg n) (extf n)). Defined.
Definition cancelL_ooextendable
             {A B C : Type} (P : C -> Type) (f : A -> B) (g : B -> C)
  : ooExtendableAlong g P -> ooExtendableAlong (g o f) P -> ooExtendableAlong f (P o g). exact (fun extg extgf n => cancelL_extendable n P f g (extg n) (extgf n)). Defined.
Definition cancelR_ooextendable
             {A B C : Type} (P : C -> Type) (f : A -> B) (g : B -> C)
  : ooExtendableAlong f (P o g) -> ooExtendableAlong (g o f) P -> ooExtendableAlong g P. exact (fun extf extgf n => cancelR_extendable n P f g (extf n.+1) (extgf n)). Defined.
Definition ooextendable_homotopic
             {A B : Type} (C : B -> Type) (f : A -> B) {g : A -> B} (p : f == g)
  : ooExtendableAlong f C -> ooExtendableAlong g C. exact (fun extf n => extendable_homotopic n C f p (extf n)). Defined.

  Parameter ReflectiveSubuniverse : Type.

  Parameter O_reflector : forall (O : ReflectiveSubuniverse),
                            Type@{i} -> Type@{i}.

  Parameter inO_internal : forall (O : ReflectiveSubuniverse),
                             Type@{i} -> Type@{i}.

  Parameter to : forall (O : ReflectiveSubuniverse@{u}) (T : Type@{i}),
                   T -> O_reflector@{u i} O T.

  Parameter extendable_to_O_internal
  : forall (O : ReflectiveSubuniverse@{u}) {P : Type@{i}} {Q : Type@{j}} {Q_inO : inO_internal@{u j} O Q},
      ooExtendableAlong (to O P) (fun _ => Q).
  Check extendable_to_O_internal@{u i j k1 k2 k3 k4 k5}.
