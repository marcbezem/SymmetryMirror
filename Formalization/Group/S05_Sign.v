(** * Section 4.5 The sign homomorphism

    Part of Chapter 4 ([group.tex]); see [Group.v] for an overview of
    the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Counting over finite types uses the library's [Finite] and [finadd]
      (sums of natural numbers over a finite type); we add [finadd_add]
      and a parity function [even] with [even_add], [even_double].
    - [BSG2] ([BΣ_2], the component of [Fin 2] in [Set]); for [T : BSG2]
      the underlying set [el2 T] has decidable equality, and two elements
      different from a third are equal ([el2_two]).
    - The parity relation [parity P] on [∏_{e:E} P(e)], for a finite [E]
      and [P : E → BΣ_2], via the number [ndis f g] of points where [f]
      and [g] disagree.
    - Lemma [lem:parityequiv]: [∼] is an equivalence relation
      ([parity_refl], [parity_symm], [parity_trans]); the quotient
      [SignQ P] is a 2-element set if [E] is (merely) nonempty
      ([SignQ_two]), and contractible if [E] is empty ([SignQ_empty]).
      Instead of the book's Venn diagram we use that, pointwise,
      [d(f,g) + d(g,h) = d(f,h) + 2·d(f,g)·d(g,h)] for the disagreement
      counts ([dis_trans]), so that parities add up ([parity_sum]).  For
      a given [f₀], [[g] ↦ even(ndis f₀ g)] is an equivalence
      [SignQ P ≃ Bool] ([phi], [SignQ_eqv_Bool]); surjectivity uses
      [f₀] changed at a single point ([flip]).
    - Definition [def:mu_E]: [mu_E : Hom(Σ_2^E, Σ_2)], with [Σ_2^E] the
      product [PiG] of Section 4.2, by deciding whether [E] is merely
      inhabited.  The pointing path identifies the class of the constant
      function [fin2_0] with [true] and then with an element of [Fin 2].
    - Definition [def:sign-ordering]: for a finite [A], [EA] (2-element
      subsets as [S : A → Bool] with two elements), [PA],
      [LocalOrdering] and [SignOrdering].

    Left out (time limit per section)
    - The exercise on [Uμ_E] (product of values), definitions [def:sgn]
      and [def:alternating-groups] (these need that [E(A)] is nonempty
      for [n ≥ 2] and the standard sign ordering of [Fin n]),
      [xca:isos_A3_C3], [def:sgn-permutation], [lem:sign-properties],
      [cor:sign-defined], [xca:sign-by-crossings], and the count [n!/2]
      of even permutations.
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Types.Sum Types.Unit Truncations.Core Spaces.Nat.Core
  Spaces.Finite.Fin Spaces.Finite.Finite Colimits.Quotient.
From SymmetryMirror Require Export Group.S04_Homomorphisms.

Local Open Scope uf_scope.

(** ** 4.5 The sign homomorphism *)

(** ** Finite sums of natural numbers

    We count with the library's [finadd] over a finite type ([Finite], the
    library's notion, equivalent to [isFinSet] by [isFinSet_Finite]). *)

Definition sigma_sum_distrib {X : Type} (Y Z : X -> Type)
  : {x : X & Y x + Z x} ≃ ({x : X & Y x} + {x : X & Z x}).
Proof.
  refine (mkEqv (fun w => match snd w with
                          | inl y => inl (fst w; y)
                          | inr z => inr (fst w; z) end)
                (fun s => match s with
                          | inl w => (fst w; inl (snd w))
                          | inr w => (fst w; inr (snd w)) end) _ _).
  - intros [x [y|z]]; exact refl.
  - intros [[x y]|[x z]]; exact refl.
Defined.

Definition finadd_add `{Funext} {X : Type} `{Finite X} (f g : X -> nat)
  : finadd (fun x => (f x + g x)%nat) = (finadd f + finadd g)%nat.
Proof.
  refine (_ @ (fcard_sigma (fun x => Fin (f x) + Fin (g x)))^ @ _).
  - apply ap. apply path_forall. intro x. exact (fcard_sum (Fin (f x)) (Fin (g x)))^.
  - refine (fcard_equiv' (Equiv_of_Eqv (sigma_sum_distrib _ _)) @ _).
    exact (fcard_sum _ _).
Defined.

(** Parity: [even n] is [yes] for even [n]. *)
Fixpoint even (n : nat) : Bool
  := match n with O => true | S n' => negb (even n') end.

Definition even_add (a b : nat) : even (a + b)%nat = (if even a then even b else negb (even b)).
Proof.
  induction a as [|a IH]; cbn.
  - exact refl.
  - rewrite IH. destruct (even a), (even b); exact refl.
Defined.

Definition even_double (k : nat) : even (k + k)%nat = true.
Proof.
  rewrite even_add. destruct (even k); exact refl.
Defined.

(** ** The parity relation *)

(** [BΣ_2], the component of [Fin 2] in [Set]: the 2-element sets. *)
Definition BSG2 : Type := component SetU (FinSetU 2).

Definition el2 (T : BSG2) : Type := fst (fst T).

Definition el2_isSet (T : BSG2) : isSet (el2 T) := snd (fst T).

Definition el2_Fin2 (T : BSG2) : ptrunc (Fin 2 = el2 T)
  := ptrunc_rec ptrunc_isProp (fun p => trunc (ap fst p)) (snd T).

Definition el2_isDecSet `{Funext} (T : BSG2) : isDecSet (el2 T)
  := ptrunc_rec (isDecSet_isProp _)
       (fun p : Fin 2 = el2 T => trp isDecSet p (Fin_isDecSet 2)) (el2_Fin2 T).

Definition el2_dec `{Funext} (T : BSG2) (x y : el2 T) : isDecidable (x = y)
  := snd (el2_isDecSet T x y).

(** In a 2-element set, two elements different from a third are equal. *)
Definition el2_two `{Funext} (T : BSG2) (x y z : el2 T)
  : x ≠ y -> y ≠ z -> x = z.
Proof.
  intros nxy nyz.
  refine (ptrunc_rec (el2_isSet T x z) _ (el2_Fin2 T)). intro p.
  revert x y z nxy nyz. destruct p. intros x y z nxy nyz.
  destruct (Fin2_elems x) as [ex|ex], (Fin2_elems y) as [ey|ey], (Fin2_elems z) as [ez|ez];
    first [ exact (ex @ ez^) | destruct (nxy (ex @ ey^)) | destruct (nyz (ey @ ez^)) ].
Defined.

Section Parity.

  Context `{Funext} {E : Type} `{Finite E} (P : E -> BSG2).

  Local Notation Pi := (forall e, el2 (P e)).

  (** The number of points at which [f] and [g] disagree. *)
  Definition dis (f g : Pi) (e : E) : nat
    := match el2_dec (P e) (f e) (g e) with inl _ => 0 | inr _ => 1 end%nat.

  Definition ndis (f g : Pi) : nat := finadd (dis f g).

  (** The parity relation [f ∼ g]: [f] and [g] disagree in an even number
      of points. *)
  Definition parity (f g : Pi) : Type := even (ndis f g) = true.

  Definition parity_isProp (f g : Pi) : isProp (parity f g)
    := fun a b => isSet_bool _ _ a b.

  Definition dis_refl (f : Pi) (e : E) : dis f f e = 0%nat.
  Proof.
    unfold dis. destruct (el2_dec (P e) (f e) (f e)) as [r|n].
    - exact refl.
    - destruct (n refl).
  Defined.

  Definition dis_symm (f g : Pi) (e : E) : dis f g e = dis g f e.
  Proof.
    unfold dis.
    destruct (el2_dec (P e) (f e) (g e)) as [r|n], (el2_dec (P e) (g e) (f e)) as [r'|n'];
      try exact refl.
    - destruct (n' r⁻¹).
    - destruct (n r'⁻¹).
  Defined.

  (** Both disagree. *)
  Definition dis2 (f g h : Pi) (e : E) : nat
    := match el2_dec (P e) (f e) (g e), el2_dec (P e) (g e) (h e) with
       | inr _, inr _ => 1 | _, _ => 0 end%nat.

  Definition dis_trans (f g h : Pi) (e : E)
    : (dis f g e + dis g h e)%nat = (dis f h e + (dis2 f g h e + dis2 f g h e))%nat.
  Proof.
    unfold dis, dis2.
    destruct (el2_dec (P e) (f e) (g e)) as [r1|n1],
      (el2_dec (P e) (g e) (h e)) as [r2|n2],
      (el2_dec (P e) (f e) (h e)) as [r3|n3]; try exact refl.
    - destruct (n3 (r2 ⋅ r1)).
    - destruct r1. destruct (n2 r3).
    - destruct r2. destruct (n1 r3).
    - destruct (n3 (el2_two (P e) _ _ _ n1 n2)).
  Defined.

  (** Lemma [lem:parityequiv], first part: [∼] is an equivalence relation. *)
  Definition parity_refl (f : Pi) : parity f f.
  Proof.
    unfold parity, ndis.
    rewrite (path_forall _ _ (dis_refl f)).
    rewrite (finadd_const E 0).
    rewrite nat_mul_zero_r. exact refl.
  Defined.

  Definition parity_symm (f g : Pi) : parity f g -> parity g f.
  Proof.
    unfold parity, ndis. rewrite (path_forall _ _ (dis_symm f g)). exact idmap.
  Defined.

  Definition parity_trans (f g h : Pi) : parity f g -> parity g h -> parity f h.
  Proof.
    unfold parity, ndis. intros a b.
    pose (e := ap even (finadd_add (dis f g) (dis g h))^
               @ ap (fun k => even (finadd k)) (path_forall _ _ (dis_trans f g h))
               @ ap even (finadd_add _ _)
               @ ap even (ap (nat_add _) (finadd_add (dis2 f g h) (dis2 f g h)))).
    rewrite even_add, even_add, even_double, a, b in e. cbn in e.
    destruct (even (finadd (dis f h))); [exact refl | exact e^].
  Defined.

End Parity.

(** ** The quotient by the parity relation *)
Section ParityQuotient.

  Context `{Univalence} {E : Type} `{Finite E} (P : E -> BSG2).

  Local Notation Pi := (forall e, el2 (P e)).

  (** Parities add up. *)
  Definition parity_sum (f g h : Pi)
    : even (ndis P f h)
      = (if even (ndis P f g) then even (ndis P g h) else negb (even (ndis P g h))).
  Proof.
    unfold ndis.
    pose (e := ap even (finadd_add (dis P f g) (dis P g h))^
               @ ap (fun k => even (finadd k)) (path_forall _ _ (dis_trans P f g h))
               @ ap even (finadd_add _ _)
               @ ap even (ap (nat_add _) (finadd_add (dis2 P f g h) (dis2 P f g h)))).
    rewrite even_add, even_add, even_double in e.
    refine (_ @ e^).
    destruct (even (finadd (dis P f h))); exact refl.
  Defined.

  Definition ndis_symm (f g : Pi) : ndis P f g = ndis P g f
    := ap finadd (path_forall _ _ (dis_symm P f g)).

  (** Sign orderings (in the general setting): [∏_e P(e) / ∼]. *)
  Definition SignQ : Type := Quotient (parity P).

  Definition SignQ_isSet : isSet SignQ := IsHSet_isSet _.

  (** Given [f₀], classes are determined by the parity of the distance to
      [f₀]. *)
  Definition phi (f0 : Pi) : SignQ -> Bool.
  Proof.
    refine (Quotient_rec _ Bool (fun g => even (ndis P f0 g)) _).
    intros g g' a. unfold parity in a.
    refine (_ @ (parity_sum f0 g g')^).
    rewrite a. destruct (even (ndis P f0 g)); exact refl.
  Defined.

  Definition phi_class (f0 g : Pi) : phi f0 (class_of _ g) = even (ndis P f0 g) := refl.

  Definition phi_inj (f0 : Pi) (x y : SignQ) : phi f0 x = phi f0 y -> x = y.
  Proof.
    revert x y.
    refine (Quotient_ind2_hprop _ _ _). intros g g' e.
    apply qglue. unfold parity.
    refine (parity_sum g f0 g' @ _).
    rewrite (ndis_symm g f0). change (even (ndis P f0 g) = even (ndis P f0 g')) in e.
    rewrite e. destruct (even (ndis P f0 g')); exact refl.
  Defined.

  (** Changing [f₀] at one point [e₀]. *)
  Definition flip (f0 : Pi) (e0 : E) (y : el2 (P e0)) : Pi
    := fun e => match dec_paths e e0 with
                | inl r => trp (fun e => el2 (P e)) r⁻¹ y
                | inr _ => f0 e end.

  Definition delta (e0 e : E) : nat := match dec_paths e e0 with inl _ => 1 | inr _ => 0 end%nat.

  Definition dis_flip (f0 : Pi) (e0 : E) (y : el2 (P e0)) (n : y ≠ f0 e0)
    : dis P f0 (flip f0 e0 y) = delta e0.
  Proof.
    apply path_forall. intro e. unfold dis, flip, delta.
    destruct (dec_paths e e0) as [r|r].
    - destruct r. change (match el2_dec (P e) (f0 e) y with inl _ => 0 | inr _ => 1 end%nat = 1%nat).
      destruct (el2_dec (P e) (f0 e) y) as [q|q].
      + destruct (n q⁻¹).
      + exact refl.
    - destruct (el2_dec (P e) (f0 e) (f0 e)) as [q|q].
      + exact refl.
      + destruct (q refl).
  Defined.

  Definition delta_eqv (e0 e : E) : Fin (delta e0 e) <~> (e = e0).
  Proof.
    unfold delta. destruct (dec_paths e e0) as [r|r].
    - refine (Equiv_of_Eqv (Eqv_of_props Fin1_isProp _ (fun _ => r) (fun _ => fin1_0))).
      intros a b. apply path_ishprop.
    - refine (Equiv_of_Eqv (Eqv_of_props (fun x : Fin 0 => match x with end) _
                (fun x : Fin 0 => match x with end) (fun q => match r q with end))).
      intros a b. apply path_ishprop.
  Defined.

  Definition finadd_delta (e0 : E) : finadd (delta e0) = 1%nat.
  Proof.
    unfold finadd.
    refine (fcard_equiv' (Y := Unit) _ @ _).
    - refine (equiv_compose' (@equiv_contr_unit _ _) (equiv_functor_sigma_id (delta_eqv e0))).
    - exact refl.
  Defined.

  (** An element of [P(e₀)] different from a given one. *)
  Definition el2_other (T : BSG2) (x : el2 T) : ptrunc {y : el2 T & y ≠ x}.
  Proof.
    refine (ptrunc_rec ptrunc_isProp _ (el2_Fin2 T)). intro p.
    revert x. destruct p. intro x.
    destruct (Fin2_elems x) as [ex|ex]; destruct ex^.
    - exact (trunc (fin2_1; fun q => inl_ne_inr _ _ q^)).
    - exact (trunc (fin2_0; fun q => inl_ne_inr _ _ q)).
  Defined.

  (** For [E] nonempty, [φ_{f₀}] is an equivalence. *)
  Definition phi_isEquiv (f0 : Pi) (ne : ptrunc E) : isEquiv (phi f0).
  Proof.
    refine (inj_surj_isEquiv (cancel_isInj isSet_bool (phi_inj f0)) _).
    intros [].
    - apply trunc. refine (class_of _ f0; _).
      exact (parity_refl P f0)^.
    - refine (ptrunc_rec ptrunc_isProp _ ne). intro e0.
      refine (ptrunc_rec ptrunc_isProp _ (el2_other (P e0) (f0 e0))). intros [y0 ny].
      apply trunc. refine (class_of _ (flip f0 e0 y0); _).
      change (no = even (finadd (dis P f0 (flip f0 e0 y0)))).
      rewrite (dis_flip f0 e0 y0 ny), finadd_delta. exact refl.
  Defined.

  Definition SignQ_eqv_Bool (f0 : Pi) (ne : ptrunc E) : SignQ ≃ Bool
    := (phi f0; phi_isEquiv f0 ne).

  (** Lemma [lem:parityequiv], second part: if [E] is nonempty, the
      quotient is a 2-element set. *)
  Definition SignQ_two (ne : ptrunc E) : ptrunc (Fin 2 = SignQ).
  Proof.
    (* an element [f₀] of [∏_e P(e)], by finite choice *)
    refine (ptrunc_rec ptrunc_isProp _
              (@finite_choice E _ (fun e => el2 (P e)) (fun _ => tt)
                 (fun e => ptrunc_rec ptrunc_isProp
                             (fun p : Fin 2 = el2 (P e) => tr (trp idmap p fin2_0))
                             (el2_Fin2 (P e))))).
    intro f0. apply trunc.
    exact (etop (Eqv_inv (SignQ_eqv_Bool f0 ne)) ⋅ Fin2_Bool_path).
  Defined.

  Definition SignQ_BSG2 (ne : ptrunc E) : BSG2
    := ((SignQ; SignQ_isSet);
        ptrunc_rec ptrunc_isProp
          (fun p : Fin 2 = SignQ =>
             trunc (path_sigma_prop (fun X => isSet_isProp X)
                      (u := FinSetU 2) (v := (SignQ; SignQ_isSet)) p))
          (SignQ_two ne)).

  (** If [E] is empty, the quotient is contractible. *)
  Definition SignQ_empty (ne : ¬ E) : isContr SignQ.
  Proof.
    pose (f0 := fun e => match ne e with end : el2 (P e)).
    refine (class_of _ f0; _).
    refine (Quotient_ind_hprop _ _ _). intro g.
    apply qglue.
    assert (r : f0 = g) by (apply path_forall; intro e; destruct (ne e)).
    destruct r. exact (parity_refl P f0).
  Defined.

End ParityQuotient.

(** Definition [def:mu_E]: [μ_E : Hom(Σ_2^E, Σ_2)], by deciding whether
    [E] is nonempty.  The classifying type of [Σ_2^E] is [E → BΣ_2],
    pointed at the constant family [Fin 2]; for [E] nonempty, [Bμ_E(P) :≡
    (∏_e P(e))/∼], pointed via [φ] at the constant function [fin2_0]. *)
Section Mu.

  Context `{Univalence} {E : Type} (hE : isFinSet E).

  #[local] Instance FE : Finite E := isFinSet_Finite hE.

  Definition P0 : E -> BSG2 := fun _ => sh (SG 2).

  Definition Bmu_pt (ne : ptrunc E) : sh (SG 2) = SignQ_BSG2 P0 ne.
  Proof.
    refine (path_sigma_prop (fun _ => ptrunc_isProp) _).
    refine (path_sigma_prop (fun X => isSet_isProp X) (u := FinSetU 2)
              (v := (SignQ P0; SignQ_isSet P0)) _).
    exact (etop (Eqv_inv (SignQ_eqv_Bool P0 (fun _ => fin2_0) ne)) ⋅ Fin2_Bool_path).
  Defined.

  Definition mu_E : Hom (PiG hE (fun _ => SG 2)) (SG 2).
  Proof.
    destruct (decidable_merely_finite E) as [ne|ne].
    - exact (@mkhom (PiG hE (fun _ => SG 2)) (SG 2)
               ((fun P => SignQ_BSG2 P ne); Bmu_pt ne)).
    - exact (@mkhom (PiG hE (fun _ => SG 2)) (SG 2) ((fun _ => sh (SG 2)); refl)).
  Defined.

End Mu.

(** Definition [def:sign-ordering]: for a finite set [A], the set [E(A)]
    of 2-element subsets (as decidable subsets [S : A → Bool] with two
    elements), the family [P] of their underlying 2-element sets, local
    orderings [∏_{e:E(A)} P(e)] and sign orderings
    [(∏_{e:E(A)} P(e))/∼]. *)
Section SignOrdering.

  Context `{Univalence} (A : Type) `{Finite A}.

  #[local] Instance Bool_Finite : Finite Bool
    := finite_equiv' (Fin 2) (Equiv_of_Eqv Fin2_Bool) _.

  Definition sub_el (S : A -> Bool) : Type := {a : A & S a = true}.

  Definition EA : Type := {S : A -> Bool & fcard (sub_el S) = 2%nat}.

  #[local] Instance EA_Finite : Finite EA.
  Proof.
    apply finite_sigma; [exact _ |]. intro S.
    apply finite_decidable_hprop; exact _.
  Defined.

  Definition sub_el_isSet (S : A -> Bool) : isSet (sub_el S) := IsHSet_isSet _.

  Definition PA (e : EA) : BSG2.
  Proof.
    refine ((sub_el (fst e); sub_el_isSet (fst e)); _).
    refine (Trunc_functor (-1) _ (merely_equiv_fin (sub_el (fst e)))). intro f.
    refine (path_sigma_prop (fun X => isSet_isProp X) (u := FinSetU 2)
              (v := (sub_el (fst e); sub_el_isSet (fst e))) _).
    refine ((etop (Eqv_of_Equiv f))⁻¹ ⋅ _).
    exact (ap Fin (snd e)⁻¹).
  Defined.

  Definition LocalOrdering : Type := forall e : EA, el2 (PA e).

  Definition SignOrdering : Type := SignQ PA.

End SignOrdering.
