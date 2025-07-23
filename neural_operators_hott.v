(** Neural Operators *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.Algebra.Matrix.
Require Import UniMath.Algebra.AbelianGroups.
Require Import UniMath.Algebra.Monoids.
Require Import UniMath.Algebra.Groups.
Require Import UniMath.Algebra.RigsAndRings.
Require Import UniMath.Algebra.Domains_and_Fields.

Require Import UniMath.RealNumbers.All.
Require Import UniMath.Topology.All.
Require Import UniMath.Algebra.Modules.
Require Import UniMath.Algebra.RigsAndRings.
Require Import UniMath.RealNumbers.NonnegativeReals.

Require Import UniMath.Algebra.Groups.

(** Work on making an easier module system *)
(* Should also have
   make_module R:ring  :module R *)
(** Goal1: (∀ R:ring) R has an abelian group. So we should just need an extractor *)

About natlth.

(* Recursively subtract b from a until a < b *)
Fixpoint nat_mod (a b : nat) : nat :=
  match a with
  | 0 => 0
  | S a' =>
    if natlth( a b) then a (* aaaaaaaaaaa *)
    else nat_mod (a - b) b
  end.

Require Import Coq.Arith.PeanoNat.
(* Define mod for natural numbers directly, since Nat.mod is available *)
Definition Z5_mul (a b : nat) : nat := (a * b) mod 5.
Definition Z5_add (a b : Datatypes.nat) : nat := (a + b) mod 5.


(* Got the set *)
Definition ring_to_2binopset(R : ring) : setwith2binop := pr1 R.

About ring_to_2binopset.
Print setwith2binop.
Print ring.

(* Define S3, the symmetric group of order 3 *)
Inductive S3 : Set :=
  | e (* identity element *)
  | s1 (* (12) *)
  | s2 (* (13) *)
  | s3 (* (23) *)
  | s4 (* (123) *)
  | s5 (* (132) *).

(* Group operation: we define a basic composition function for the group elements *)
Definition S3_op (a b : S3) : S3 :=
  match a, b with
  | e, x => x
  | x, e => x
  | s1, s1 => e
  | s2, s2 => e
  | s3, s3 => e
  | s4, s5 => e
  | s5, s4 => e
  (* Add additional cases as needed to handle all compositions *)
  | _, _ => e  (* handle other cases generically *)
  end.

(* Define S3 as a group with one binary operation *)
Record group := mk_group {
  carrier : Type;
  op : carrier -> carrier -> carrier;
}.

(* S3_group: carrier is S3 and operation is S3_op *)
Definition S3_group : group := mk_group S3 S3_op.

(* Addition and multiplication modulo 5 *)
Definition Z5_add (a b : nat) : nat := (a + b) mod 5.
Definition Z5_mul (a b : nat) : nat := (a * b) mod 5.

(* Define a record type for rings with two binary operations *)
Record ring := mk_ring {
  carrier : Type;
  add : carrier -> carrier -> carrier;
  mul : carrier -> carrier -> carrier;
}.

(* Z5_ring: carrier is nat (natural numbers) and operations are mod 5 add/mul *)
Definition Z5_ring : ring := mk_ring nat Z5_add Z5_mul.



Definition ring_to_2binopset(R : ring) : setwith2binop := pr1 R.

(* Got the abelian group operation + *)
Definition oper1 (R : ring) : binop R := pr1 (pr2 (underlying_set_with_2binop R)).

About oper1.
Print oper1.
Print abgr.
About isabgrop.
Print isabgrop.

(* will not simply take this format... *)
Definition ring_to_abgr (R : ring) : abgr := ∑ underlying_set_with_2binop R, 
isabgrop (oper1 R).


About module.
About module_struct.
About ringfun.
About ringofendabgr.  (** The set of endomorphisms of an abelian group is a ring *)
About make_ring.
About make_setwithbinop.
About isringops.
About binop.
About ring.
Print ring.
(* pr1? projection of argument 1 from a double i.e. pr1 : (a,b) |-> a *)
About pr1.
(* homotopy set *)
About hSet.
(** Unsafe universe (In reality UU : Type, it is called "unsafe" 
  because it is a class from NBG set theory) *)
About UU.

(* Define the carrier type of the direct sum of two abelian groups *)
Definition directsum_abgr_carrier (G H : abgr) : hSet :=
  setdirprod (pr1 G) (pr1 H).


(* Define the binary operation for the direct sum *)

(* Define the identity element (zero) for the direct sum *)
Definition directsum_abgr_zero {G H : abgr} : directsum_abgr_carrier G H :=
  make_dirprod (unel G) (unel H).


(* Finally, define the direct sum of two abelian groups *)
(*
Definition directsum_abgr (G H : abgr) : abgr :=
  make_abgr (make_setwithbinop (directsum_abgr_carrier G H) directsum_abgr_op) (directsum_abgr_isabgr G H).


Definition easy_module_constructor (R : ring) : module R.
Proof.
  (* Define the abelian group Z^3 (i.e., direct product of Z with itself) *)
  (* Use existing functions from the UniMath library to create this abelian group *)
  set (G := directsum_abgr Z (directsum_abgr Z Z)).

  (* Now, define the ring action on the abelian group G *)
  (* Use the module_struct definition to create the module structure *)
  exact (make_module G (mult_to_module_struct (* appropriate properties here *))).
Defined.
*)

(* end module system *)

(* Access the real number type from UniMath *)
Definition ℝ := Reals.
Definition R := Reals. (* really lazy, but why not *)

(* This set is needed in order to refer to operators using syntactic sugar *)
Declare Scope R_scope.
Delimit Scope R_scope with R.
Local Open Scope R_scope.

Infix "+" := Rplus : R_scope.
Infix "-" := Rminus : R_scope.
Infix "*" := Rmult : R_scope.
Notation "- x" := (Ropp x) : R_scope.
Notation "/ x" := (Rinv (pr1 x) (pr2 x)) : R_scope.
Notation "x / y" := (Rdiv x (pr1 y) (pr2 y)) : R_scope.

(** Prove various basic properties about real numbers, or reprove *)

(* Test commutativity of real numbers *)
Goal ∏ (a b : R), a + b = b + a. 
Proof.
  intros a b.
  apply iscomm_Rplus.  (* Commutes under addition *)
Qed.

(* Test that 0 is the additive identity *)
Goal ∏ (a : R), a + 0 = a.
Proof.
  intros a.
  apply isrunit_Rzero_Rplus.  (* Left identity under addition for Reals *)
Qed.

(* Test multiplication commutativity of real numbers *)
Goal ∏ (a b : R), a * b = b * a.
Proof.
  intros a b.
  apply iscomm_Rmult.  (* Commutes under multiplication *)
Qed.

(* Test associativity of multiplication *)
Goal ∏ (a b c : Reals), a * (b * c) = (a * b) * c.
Proof.
  intros a b c.
  rewrite isassoc_Rmult.  (* Using setoid_rewrite to rewrite under associativity *)
  reflexivity.
Qed.


(* Extract the ring and group from the constructive field of real numbers *)
(* both are needed to construct modules, for some reason 
   It is usually the case that a module is a ring that "acts" or operates
   on a ring (in our case a field). *)
Definition Rring : ring := pr1 Reals.
Definition Rgroup : abgr := pr1 Reals.

Print Rring.



(* Definition R := pr1hSet R. *)
(* Define R³ as a 3-dimensional vector space *)
Definition R3 := dirprod Rring (dirprod Rring Rring). 
(* Definition R2 := total2 (λ x : Rring, total2 (λ y : Rring, Rring)). *)

Print R3.

(* Define addition for R³ *)
Definition add_R3 (v1 v2 : R3) : R3 :=
  tpair _ 
        (* Addition of the first components *)
    (Rplus (pr1 v1) (pr1 v2))  
     (tpair _ 

      (* Addition of the second components *)
      (Rplus (pr1 (pr2 v1)) (pr1 (pr2 v2)))  

      (* Addition of the third components *)
      (Rplus (pr2 (pr2 v1)) (pr2 (pr2 v2)))  
    ).

(* Define scalar multiplication for R³ *)
Definition smult_R3 (r : Rring) (v : R3) : R3 :=
  tpair _ 
       
    (* Scalar multiplication of the first component *)
    (Rmult r (pr1 v))  
    (tpair _ 

       (* Scalar multiplication of the second component *)
      (Rmult r (pr1 (pr2 v)))  

      (* Scalar multiplication of the third component *)
      (Rmult r (pr2 (pr2 v)))  
    ).



(* Function to convert nat to R using nat_to_NonnegativeReals and 
   make_dirprod *)
Definition nat_to_R (n : nat) : R :=
  NR_to_hr (make_dirprod (nat_to_NonnegativeReals n) 0%NR).


Definition x : R := (nat_to_R 1).
Print x.

(* Helper function to create a vector in R3 *)
Definition make_R3 (x y z : nat) : R3 :=
  make_dirprod (nat_to_R x) (make_dirprod (nat_to_R y) (nat_to_R z)).

(* Example vectors in R³ *)
(*Definition v1 : R3 := make_dirprod (nat_to_R 1) (make_dirprod (nat_to_R 2) (nat_to_R 3)). *)


Definition v1 : R3 := make_R3 1 2 3.
(* Another example vector v2 in R3 *)
Definition v2 : R3 := make_R3 4 5 6.

Print v1.

(* Example scalar *)
Definition scalar : Rring := nat_to_R 2.

(** computation for actual reals causes compiler-hang *)
(*
  (* Test scalar multiplication: scalar * v1 *)
  Compute (smult_R3 scalar v1).

  (* Test vector addition: v1 + v2 *)
  Compute (add_R3 v1 v2).
*)

(** So the plan is a conversion process between different numerical types *)

(** Integer constructions *)

Definition Z := hz.
Definition Zring : ring := hz.
(* the needed albelian group for integers ends up being a pain *)

(* ℤ³ as a total2 type (Σ-type) *)
Definition Z3_carrier := total2 (λ _: hz, total2 (λ _: hz, hz)).
(* Definition Z3_carrier := (Z × Z × Z)%type. *)

(* Addition in ℤ³ *)
Definition Z3_plus (v1 v2 : Z3_carrier) : Z3_carrier :=
  match v1, v2 with
  | tpair _ x1 (tpair _ y1 z1), tpair _ x2 (tpair _ y2 z2) =>
      tpair _ (x1 + x2)%hz (tpair _ (y1 + y2)%hz (z1 + z2)%hz)
  end.

(*
(* failed *)
Definition Z3_plus (v1 v2 : Z3_carrier) : Z3_carrier :=
  match v1, v2 with
  | make_dirprod x1 (make_dirprod y1 z1), make_dirprod x2 (make_dirprod y2 z2) =>
      make_dirprod (x1 + x2)%hz (make_dirprod (y1 + y2)%hz (z1 + z2)%hz)
  end.


(* failed Addition in ℤ³ *)
Definition Z3_plus (v1 v2 : Z3_carrier) : Z3_carrier :=
  match v1, v2 with
  | (x1, y1, z1), (x2, y2, z2) => (x1 + x2, y1 + y2, z1 + z2)
  end.
*)
(* Zero element in ℤ³ *)
Definition Z3_zero : Z3_carrier := tpair _ 0%hz (tpair _ 0%hz 0%hz).

(* Inverse element in ℤ³ *)
Definition Z3_inv (v : Z3_carrier) : Z3_carrier :=
  match v with
  | tpair _ x (tpair _ y z) =>
      tpair _ (-x)%hz (tpair _ (-y)%hz (-z)%hz)
  end.

(* Scalar multiplication in ℤ³ *)
Definition Z3_smult (n : hz) (v : Z3_carrier) : Z3_carrier :=
  match v with
  | tpair _ x (tpair _ y z) =>
      tpair _ (n * x)%hz (tpair _ (n * y)%hz (n * z)%hz)
  end.


(* Fail to Define ℤ³ as an abelian group *)
(*
Definition Z3_abgr : abgr :=
  make_abgr (make_setwithbinop Z3_carrier Z3_plus) Z3_is_abgroup.
*)

(* Fail to Prove that ℤ³ forms an abelian group *)
(*
Definition Z3_is_abgr : isabgr Z3_carrier :=
  make_isabgr Z3_plus Z3_zero Z3_inv.
*)

(* Fail to make ℤ³ as a module over ℤ *)
(*
Definition Z3_module_struct : module_struct Z Z3_carrier :=
  make_module_struct Z3_smult.
*)

(*
*)(*
(* failed Zero element in ℤ³ *)
Definition Z3_zero : Z3_carrier := (0, 0, 0).

(* failed Inverse element in ℤ³ *)
Definition Z3_inv (v : Z3_carrier) : Z3_carrier :=
  match v with
  | (x, y, z) => (-x, -y, -z)
  end.
*)


(* Proof that Z3 is an abelian group *)
(*
Definition Z3_is_abgroup : isabgr Z3_carrier :=
  make_isabgr Z3_plus Z3_zero Z3_inv.
*)

(*
Definition Z3_module : module Zring :=
  make_module Z3_abgr Z3_module_struct.
*)

(* Making an attempt to do a constructive comparison in Real *)
(*
Axiom Rlt_dec : forall r1 r2 : R, {Rlt r1 r2} + {~Rlt r1 r2}. 
*)

(* Import integer functions that go beyond 23 *)
Require Import Coq.ZArith.ZArith.  

(* Define the floor function with a comparison function *)
(*
Fixpoint floor_R_aux (r : R) (n : nat) : nat :=
  if (Rlt r (nat_to_R (S n)))  (* Use Rlt_dec for real number comparison *)
  then n
  else floor_R_aux r (S n).

(* Main floor function starting from 0 *)
Definition floor_R (r : R) : nat :=
  floor_R_aux r 0.
*)





(* Define the norm function for R³ *)
(*
Definition norm_R3 (v : VectorSpace_R ) : Real.
*)


(** Start of some more useful code *)

(* Using real numbers as weights, for simplicity *)
Definition Weight := R. 

(* Define a basic neural operator as a map from an input type to an output type. *)
Definition NeuralOperator (X Y : Type) : Type :=
  Weight -> X -> Y. (* Weight x X -> Y *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Algebra.Monoids.
Require Import UniMath.Algebra.Modules.

(** Sketch of Neural operators *)
(*
(* Defining the input domain D and output codomain D' *)
Definition D : hSet := hSetpair (realfun (λ x : R, True)) (isaset_real).
Definition D' : hSet := hSetpair (realfun (λ x : R, True)) (isaset_real).

(* Define function space A *)
Definition A (da : nat) := realfun (λ (x : D), hfiber (λ y : R, da)).

(* Lifting: Map input space A to hidden space using a pointwise function *)
Definition lifting (da dv0 : nat) (a : A da) : A dv0 :=
  fun x : D => maponpaths (λ y : R, y * 1%ring) (a x).  (* Simplified map *)

(* Define the hidden space iterations (kernel integration with bias and nonlinearity) *)
Definition kernel_operator (t : nat) (vt : A t) : A t :=
  fun x : D => maponpaths (λ y : R, y + 1%ring) (vt x).  (* Example local operator *)
Definition iterative_kernel_integration (T : nat) (v0 : A 1) : A T :=
  let rec_integration (vt : A 1) (t : nat) := kernel_operator t vt in
  rec_integration v0 T.

(* Projection: Map last hidden representation to output space U *)
Definition projection (dvT du : nat) (vT : A dvT) : U du :=
  fun x : D' => maponpaths (λ y : R, y * 1%ring) (vT x).

(* Full architecture Gθ *)
Definition neural_operator (T : nat) (da du : nat) (a : A da) : U du :=
  let v0 := lifting da (da + 1) a in
  let vT := iterative_kernel_integration T v0 in
  projection (da + 1) du vT.

(* Example neural operator *)
Compute (neural_operator 5 1 1 (λ x, x + 1%ring)).

*)
