(* -*- mode: coq; coq-prog-args: ("-emacs" "-indices-matter" "-nois") -*- *)
(* File reduced by coq-bug-finder from original input, then from 8858 lines to 268 lines, then from 249 lines to 207 lines *)
(* coqc version trunk (December 2014) compiled on Dec 10 2014 12:26:15 with OCaml 4.01.0
   coqtop version cagnode15:/afs/csail.mit.edu/u/j/jgross/coq-trunk,trunk (c938cb8e85f741ce697e7486d35c27c1aa31fe7a) *)

Global Set Universe Polymorphism.
Generalizable All Variables.
Require Import Coq.Init.Notations.
Notation "A -> B" := (forall (_ : A), B) : type_scope.
Open Scope type_scope.
Inductive False := .
Axiom proof_admitted : False.
Ltac admit := destruct proof_admitted.
Record prod (A B : Type) := pair { fst : A ; snd : B }.
Notation "x * y" := (prod x y) : type_scope.
Inductive nat : Set := O | S (_ : nat).
Record sigT {A} (P : A -> Type) := existT { projT1 : A ; projT2 : P projT1 }.
Notation "{ x : A  & P }" := (sigT (fun x:A => P)) : type_scope.
Notation idmap := (fun x => x).
Definition compose {A B C : Type} (g : B -> C) (f : A -> B) := fun x => g (f x).
Notation "g 'o' f" := (compose g f) (at level 40, left associativity) : function_scope.
Open Scope function_scope.
Definition composeD {A B C} (g : forall b, C b) (f : A -> B) := fun x : A => g (f x).
Notation "g 'oD' f" := (composeD g f) (at level 40, left associativity) : function_scope.
Inductive paths {A : Type} (a : A) : A -> Type := idpath : paths a a.
Arguments idpath {A a} , [A] a.
Notation "x = y :> A" := (@paths A x y) : type_scope.
Notation "x = y" := (x = y :>_) : type_scope.
Delimit Scope path_scope with path.
Local Open Scope path_scope.
Notation "1" := idpath : path_scope.
Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y.
  exact (match p with idpath => idpath end).
Defined.
Definition pointwise_paths {A} {P:A->Type} (f g:forall x:A, P x)
  := forall x:A, f x = g x.
Notation "f == g" := (pointwise_paths f g) (at level 70, no associativity) : type_scope.
Definition apD10 {A} {B:A->Type} {f g : forall x, B x} (h:f=g)
: f == g.
  exact (fun x => match h with idpath => 1 end).
Defined.
Class IsEquiv {A B : Type} (f : A -> B) := { equiv_inv : B -> A }.
Record Equiv A B := BuildEquiv {
                        equiv_fun : A -> B ;
                        equiv_isequiv : IsEquiv equiv_fun
                      }.
Coercion equiv_fun : Equiv >-> Funclass.
Global Existing Instance equiv_isequiv.
Notation "A <~> B" := (Equiv A B) (at level 85) : equiv_scope.
Notation "f ^-1" := (@equiv_inv _ _ f _) (at level 3, format "f '^-1'") : equiv_scope.
Class Contr_internal (A : Type) := BuildContr {
                                       center : A ;
                                       contr : (forall y : A, center = y)
                                     }.
Inductive trunc_index : Type :=
| minus_two : trunc_index
| trunc_S : trunc_index -> trunc_index.

Notation "n .+1" := (trunc_S n) (at level 2, left associativity, format "n .+1") : trunc_scope.
Local Open Scope trunc_scope.
Notation "-2" := minus_two (at level 0) : trunc_scope.
Notation "-1" := (-2.+1) (at level 0) : trunc_scope.

Fixpoint IsTrunc_internal (n : trunc_index) (A : Type) : Type :=
  match n with
    | -2 => Contr_internal A
    | n'.+1 => forall (x y : A), IsTrunc_internal n' (x = y)
  end.

Class IsTrunc (n : trunc_index) (A : Type) : Type :=
  Trunc_is_trunc : IsTrunc_internal n A.
Notation IsHProp := (IsTrunc -1).

Ltac simple_induction n n' IH :=
  generalize dependent n;
  fix IH 1;
  intros [| n'];
  [ clear IH | specialize (IH n') ].
Axiom isequiv_apD10 : forall (A : Type) (P : A -> Type) f g, IsEquiv (@apD10 A P f g).

Inductive Unit : Set := tt : Unit.

Definition hfiber {A B : Type} (f : A -> B) (y : B) := { x : A & f x = y }.
Local Open Scope equiv_scope.

Global Instance isequiv_idmap (A : Type) : IsEquiv idmap | 0 :=
  Build_IsEquiv A A idmap idmap.
Definition equiv_idmap (A : Type) : A <~> A.
  exact (BuildEquiv A A idmap _).
Defined.
Definition equiv_compose' {A B C : Type} (g : B <~> C) (f : A <~> B)
: A <~> C.
  admit.
Defined.

Section EquivInverse.

  Context {A B : Type} (f : A -> B) {feq : IsEquiv f}.
  Global Instance isequiv_inverse : IsEquiv f^-1 | 10000.
  admit.
  Defined.
End EquivInverse.

Theorem equiv_inverse {A B : Type} : (A <~> B) -> (B <~> A).
  admit.
Defined.

Definition trunc_equiv A {B} (f : A -> B)
           `{IsTrunc n A} `{IsEquiv A B f}
: IsTrunc n B.
  admit.
Defined.

Definition equiv_apD10  {A : Type} (P : A -> Type) f g
: (f = g) <~> (f == g)
  := BuildEquiv _ _ (@apD10 A P f g) _.
Definition equiv_path_forall `{P : A -> Type} (f g : forall x, P x)
: (f == g)  <~>  (f = g).
  admit.
Defined.
Definition equiv_functor_forall' `{P : A -> Type} `{Q : B -> Type}
           (f : B <~> A) (g : forall b, P (f b) <~> Q b)
: (forall a, P a) <~> (forall b, Q b).
  admit.
Defined.

Definition equiv_functor_prod' {A A' B B' : Type} (f : A <~> A') (g : B <~> B')
: A * B <~> A' * B'.
  admit.
Defined.

Definition equiv_functor_sigma' `{P : A -> Type} `{Q : B -> Type}
           (f : A <~> B)
           (g : forall a, P a <~> Q (f a))
: sigT P <~> sigT Q.
  admit.
Defined.

Fixpoint PathSplit (n : nat) `(f : A -> B) : Type
  := match n with
       | O => Unit
       | S n => (forall a, hfiber f a) *
                forall (x y : A), PathSplit n (@ap _ _ f x y)
     end.

Lemma equiv_functor_pathsplit (n : nat) {A B C D}
      (f : A -> B) (g : C -> D) (h : A <~> C) (k : B <~> D)
      (p : g o h == k o f)
: PathSplit n f <~> PathSplit n g.
  admit.
Defined.
Definition ooPathSplit `(f : A -> B) : Type.
  exact (forall n, PathSplit n f).
Defined.

Global Instance ishprop_oopathsplit `(f : A -> B)
: IsHProp (ooPathSplit f).
admit.
Defined.

Definition ExtensionAlong {A B : Type} (f : A -> B)
           (P : B -> Type) (d : forall x:A, P (f x))
  := { s : forall y:B, P y & forall x:A, s (f x) = d x }.

Fixpoint ExtendableAlong
         (n : nat) {A : Type@{i}} {B : Type@{j}}
         (f : A -> B) (C : B -> Type@{k}) : Type@{l}
  := match n with
       | O => Unit : Type@{l}
       | S n => (forall (g : forall a, C (f a)),
                   ExtensionAlong@{i j k l l} f C g) *
                forall (h k : forall b, C b),
                  ExtendableAlong n f (fun b => h b = k b)
     end.

Definition equiv_extendable_pathsplit  (n : nat)
           {A B : Type} (C : B -> Type) (f : A -> B)
: ExtendableAlong n f C
                  <~> PathSplit n (fun (g : forall b, C b) => g oD f).
Proof.
  generalize dependent C; simple_induction n n IHn; intros C.
  1:apply equiv_idmap.
  apply equiv_functor_prod'; simpl.
  -
    refine (equiv_functor_forall' (equiv_idmap _) _); intros g; simpl.
    refine (equiv_functor_sigma' (equiv_idmap _) _); intros rec.
    apply equiv_path_forall.
  -
    refine (equiv_functor_forall' (equiv_idmap _) _); intros h.
    refine (equiv_functor_forall' (equiv_idmap _) _); intros k; simpl.
    refine (equiv_compose' _ (IHn (fun b => h b = k b))).
    apply equiv_inverse.
    refine (equiv_functor_pathsplit n _ _
                                    (equiv_apD10 _ _ _) (equiv_apD10 _ _ _) _).
    intros []; reflexivity.
Defined.
Definition ooExtendableAlong
           {A : Type@{i}} {B : Type@{j}}
           (f : A -> B) (C : B -> Type@{k}) : Type@{l}.
  exact (forall n, ExtendableAlong@{i j k l} n f C).
Defined.

Definition equiv_ooextendable_pathsplit
           {A B : Type} (C : B -> Type) (f : A -> B)
: ooExtendableAlong f C <~>
                    ooPathSplit (fun (g : forall b, C b) => g oD f).
Proof.
  refine (equiv_functor_forall' (equiv_idmap _) _); intros n.
  apply equiv_extendable_pathsplit.
Defined.

Global Instance ishprop_ooextendable
       {A B : Type} (C : B -> Type) (f : A -> B)
: IsHProp (ooExtendableAlong f C).
Proof.
  refine (trunc_equiv _ (equiv_ooextendable_pathsplit C f)^-1).
Defined.
Check ishprop_ooextendable@{a a i i i i}.
