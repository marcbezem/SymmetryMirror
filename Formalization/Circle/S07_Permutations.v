(** * Section 3.7 Interlude: combinatorics of permutations

    Part of Chapter 3 ([circle.tex]); see [Circle.v] for an overview of
    the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - For a decidable set [A]: fixed points, moved elements and the
      support of a permutation ([def:support-permutation]); the exercise
      that permutations with disjoint supports commute
      ([disjoint_commute]).
    - Transpositions [(a b)] ([transp]), which are involutions.
    - Cyclic permutations [(a₁ ⋯ a_k)] for a list of pairwise distinct
      elements ([cyc]), and exercise [xca:perm-prod-transpositions]:
      [(a₁ a₂ ⋯ a_k) = (a₁ a_k)⋯(a₁ a₂)] ([cyc_transps]), from the step
      [(a₁ a₂ a₃ ⋯ a_k) = (a₁ a₃ ⋯ a_k)(a₁ a₂)].
    - Exercise [xca:factorial]: a finite set of cardinality [n] has [n!]
      permutations ([card_Aut]), via the library's [fcard_aut].

    Left out
    - Remark [rem:cycle-vs-cycle] (informal), the corollary that every
      permutation of a finite set is a composition of transpositions
      (it needs the decomposition into disjoint cycles), and the exercise
      on binomial coefficients and the number of [k]-cycles. *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core Spaces.Nat.Core Spaces.Int
  Spaces.Circle Spaces.Finite.Fin Spaces.Finite.Finite Spaces.List.Core.
From SymmetryMirror Require Export Circle.S06_ConnCoverings.

Local Open Scope uf_scope.

(** ** 3.7 Interlude: combinatorics of permutations *)

Section Permutations.

  Context `{Funext} {A : Type} (dA : isDecSet A).

  Definition deceq (a b : A) : isDecidable (a = b) := snd (dA a b).

  Definition not_not_eq {a b : A} (nn : ¬ ¬ (a = b)) : a = b
    := match deceq a b with inl e => e | inr n => match nn n with end end.

  (** Definition [def:support-permutation]: fixed points, moved elements and
      the support of a permutation. *)
  Definition fixed (σ : A ≃ A) (a : A) : Type := fst σ a = a.

  Definition moved (σ : A ≃ A) (a : A) : Type := ¬ fixed σ a.

  Definition support (σ : A ≃ A) : Type := {a : A & moved σ a}.

  Definition moved_dec (σ : A ≃ A) (a : A) : isDecidable (moved σ a)
    := match deceq (fst σ a) a with
       | inl e => inr (fun n => n e)
       | inr n => inl n
       end.

  Definition moved_image (σ : A ≃ A) (a : A) (m : moved σ a) : moved σ (fst σ a)
    := fun e => m (Eqv_inj σ e).

  (** Exercise: permutations with disjoint supports commute. *)
  Definition disjoint (σ τ : A ≃ A) : Type := forall a, ¬ (moved σ a × moved τ a).

  Definition disjoint_commute (σ τ : A ≃ A) (d : disjoint σ τ)
    : fst σ ∘ fst τ = fst τ ∘ fst σ.
  Proof.
    apply ptw_inv. intro a. unfold comp.
    destruct (deceq (fst σ a) a) as [e|n].
    - destruct (deceq (fst τ a) a) as [e'|n'].
      + exact ((ap (fst σ) e' @ e) @ (ap (fst τ) e @ e')^).
      + assert (f : fst σ (fst τ a) = fst τ a)
          by exact (not_not_eq (fun ns => d (fst τ a) (ns; moved_image τ a n'))).
        exact (f @ (ap (fst τ) e)^).
    - assert (f : fst τ (fst σ a) = fst σ a)
        by exact (not_not_eq (fun nt => d (fst σ a) (moved_image σ a n; nt))).
      assert (g : fst τ a = a) by exact (not_not_eq (fun nt => d a (n; nt))).
      exact (ap (fst σ) g @ f^).
  Defined.

  (** Transpositions [(a b)]. *)
  Definition transp (a b : A) (x : A) : A
    := match deceq x a with
       | inl _ => b
       | inr _ => match deceq x b with inl _ => a | inr _ => x end
       end.

  Definition transp_invol (a b x : A) : transp a b (transp a b x) = x.
  Proof.
    unfold transp at 2.
    destruct (deceq x a) as [ea|na].
    - unfold transp. destruct (deceq b a) as [eba|nba].
      + exact (eba @ ea^).
      + destruct (deceq b b) as [_|nbb]; [exact ea^ | destruct (nbb refl)].
    - destruct (deceq x b) as [eb|nb].
      + unfold transp. destruct (deceq a a) as [_|naa]; [exact eb^ | destruct (naa refl)].
      + unfold transp. destruct (deceq x a) as [ea|_]; [destruct (na ea)|].
        destruct (deceq x b) as [eb|_]; [destruct (nb eb) | exact refl].
  Defined.

  Definition transpEqv (a b : A) : A ≃ A
    := mkEqv (transp a b) (transp a b) (transp_invol a b) (transp_invol a b).

  (** Cyclic permutations [(a₁ a₂ ⋯ a_k)], for a list of pairwise distinct
      elements: [a_i ↦ a_{i+1}], [a_k ↦ a₁], other elements fixed.  We give
      it by [next l h x], which maps an element of [l] to its successor in
      [l], the last element to [h], and fixes elements not in [l]. *)
  Fixpoint next (l : list A) (h x : A) : A
    := match l with
       | nil => x
       | cons b r => match deceq x b with
                     | inl _ => match r with nil => h | cons c _ => c end
                     | inr _ => next r h x
                     end
       end.

  Definition cyc (a1 : A) (r : list A) : A -> A := next (cons a1 r) a1.

  Fixpoint notin (x : A) (l : list A) : Type
    := match l with nil => Unit | cons b r => (x ≠ b) × notin x r end.

  Fixpoint distinct (l : list A) : Type
    := match l with nil => Unit | cons b r => notin b r × distinct r end.

  Definition next_notin (l : list A) (h x : A) (n : notin x l) : next l h x = x.
  Proof.
    induction l as [|b r IH].
    - exact refl.
    - cbn. destruct (deceq x b) as [e|_]; [destruct (fst n e) | exact (IH (snd n))].
  Defined.

  (** [next (b :: r)] differs from [next r] only at [b] and at the last
      element of [r]. *)
  Definition next_cons_ne (b c : A) (r : list A) (h x : A) (nb : x ≠ b)
    : next (cons b (cons c r)) h x = next (cons c r) h x.
  Proof. cbn. destruct (deceq x b) as [e|_]; [destruct (nb e) | exact refl]. Defined.

  (** Exercise [xca:perm-prod-transpositions]:
      [(a₁ a₂ ⋯ a_k) = (a₁ a_k)(a₁ a_{k-1})⋯(a₁ a₂)], from the step
      [(a₁ a₂ a₃ ⋯ a_k) = (a₁ a₃ ⋯ a_k)(a₁ a₂)]. *)
  Fixpoint transps (a1 : A) (r : list A) : A -> A
    := match r with
       | nil => idmap
       | cons b r' => fun x => transps a1 r' (transp a1 b x)
       end.


  Definition cyc_step (a1 a2 : A) (r : list A) (n12 : a1 ≠ a2) (n2 : notin a2 r) (x : A)
    : cyc a1 (cons a2 r) x = cyc a1 r (transp a1 a2 x).
  Proof.
    unfold cyc, transp.
    destruct (deceq x a1) as [e1|n1].
    - destruct e1. cbn. destruct (deceq x x) as [_|nxx]; [|destruct (nxx refl)].
      destruct (deceq a2 x) as [e|_]; [destruct (n12 e^)|].
      exact (next_notin r x a2 n2)^.
    - destruct (deceq x a2) as [e2|n2'].
      + destruct e2. cbn.
        destruct (deceq x a1) as [e|_]; [destruct (n1 e)|].
        destruct (deceq x x) as [_|nxx]; [|destruct (nxx refl)].
        destruct (deceq a1 a1) as [_|naa]; [exact refl | destruct (naa refl)].
      + cbn. destruct (deceq x a1) as [e|_]; [destruct (n1 e)|].
        destruct (deceq x a2) as [e|_]; [destruct (n2' e) | exact refl].
  Defined.

  Definition cyc_transps (a1 : A) (r : list A) (dr : distinct (cons a1 r)) (x : A)
    : cyc a1 r x = transps a1 r x.
  Proof.
    revert x. induction r as [|b r IH]; intro x.
    - unfold cyc. cbn. destruct (deceq x a1) as [e|_]; [exact e^ | exact refl].
    - refine (cyc_step a1 b r (fst (fst dr)) (fst (snd dr)) x @ _).
      exact (IH (snd (fst dr); snd (snd dr)) _).
  Defined.

End Permutations.

(** Exercise [xca:factorial]: a finite set of cardinality [n] has [n!]
    permutations, via the library's [fcard_aut]. *)
Definition Aut (X : Type) : Type := X ≃ X.

Definition Aut_isFinSet `{Univalence} {X : Type} (h : isFinSet X) : isFinSet (Aut X)
  := isFinSet_Eqv (Eqv_inv (Equiv_Eqv_eqv X X))
       (Finite_isFinSet (@finite_aut _ X (isFinSet_Finite h))).

Definition card_Aut `{Univalence} {X : Type} (h : isFinSet X)
  : cardF (Aut_isFinSet h) = fact (cardF h).
Proof.
  refine (cardF_fcard _ @ _ @ ap fact (cardF_fcard h)^).
  refine (_ @ @fcard_aut _ X (isFinSet_Finite h)).
  exact (@fcard_equiv' _ _ (Equiv_of_Eqv (Eqv_inv (Equiv_Eqv_eqv X X))) _ _).
Defined.
