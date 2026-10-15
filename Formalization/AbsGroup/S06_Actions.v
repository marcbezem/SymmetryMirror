(** * Section 6.6 Actions, from abstract to concrete and back

    Part of Chapter 6 ([absgroup.tex]); see [AbsGroup.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Inverses of abstract isomorphisms ([AbsIso_inv]) and postcomposition
      with an isomorphism as an equivalence ([absHom_postcomp]).
    - [abstr(Σ_S) ≅ Perm(S)] ([SG_Perm_iso]), using [idtoeqv_trans].
    - Lemma [lem:actionsconcr2abstr]: [GSet G ≃ absGSet(abstr G)]
      ([actions_eqv]), by the book's chain of equivalences through
      [GSet_eqv] (Section 5.2) and [abstr_hom_eqv] (Section 6.5); the
      underlying set of [ev(X)] is [X(sh_G)] by definition
      ([actions_eqv_set]).

    Left out (time limit per result)
    - Example [ex:abstrandconj] and lemma [lem:abstrandconj], exercises
      [xca:f^*-abs(f)^*] and [xca:f_!-abs(f)_!].
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core.
From SymmetryMirror Require Export AbsGroup.S05_Homomorphisms.

Local Open Scope uf_scope.

(** ** 6.6 Actions, from abstract to concrete and back *)

(** Inverse and composition of abstract isomorphisms. *)
Definition AbsIso_inv {A B : AbsGroup} (i : AbsIso A B) : AbsIso B A.
Proof.
  refine (Eqv_inv (fst i); _). intros x y. cbn.
  apply (isInj_cancel (isEquiv_isInj (snd (fst i)))).
  refine (eqinv_r (snd (fst i)) _ @ _). refine (_ @ (snd i _ _)^).
  exact (ap011 (ag_mul B) (eqinv_r (snd (fst i)) x)^ (eqinv_r (snd (fst i)) y)^).
Defined.

(** Postcomposition with an isomorphism is an equivalence of the sets of
    homomorphisms. *)
Definition absHom_postcomp `{Funext} (K : AbsGroup) {A B : AbsGroup} (i : AbsIso A B)
  : absHom K A ≃ absHom K B.
Proof.
  pose (i' := ((fst (fst i); snd i) : absHom A B)).
  pose (j := (fst (fst (AbsIso_inv i)); snd (AbsIso_inv i)) : absHom B A).
  refine (mkEqv (absHom_comp i') (absHom_comp j) _ _); intro f.
  - apply path_absHom. intro s. exact (eqinv_l (snd (fst i)) _).
  - apply path_absHom. intro s. exact (eqinv_r (snd (fst i)) _).
Defined.

(** [abstr(Σ_S)] is isomorphic to the abstract permutation group of [S]. *)
Definition idtoeqv_trans `{Funext} {X Y Z : Type} (p : X = Y) (q : Y = Z)
  : idtoeqv (q ⋅ p) = Eqv_comp (idtoeqv p) (idtoeqv q).
Proof. destruct q, p. apply path_Eqv. exact refl. Defined.

Definition SG_Perm_iso `{Univalence} (S : SetU) : AbsIso (abstr (SG_S S)) (ag_Perm S).
Proof.
  refine (Eqv_comp (USym_SG_S_eqv S) (idtoeqv; ua _ _); _).
  intros u v. cbn.
  refine (ap idtoeqv (ap (ap fst) (ap_trans fst v u) @ ap_trans fst _ _) @ _).
  exact (idtoeqv_trans _ _).
Defined.

(** Lemma [lem:actionsconcr2abstr]: [G-Set ≃ abstr(G)-Set], by the chain
    [G-Set ≃ ∑_S Hom(G, Σ_S) ≃ ∑_S absHom(abstr G, abstr Σ_S)
     ≃ ∑_S absHom(abstr G, Perm(S))]. *)
Definition actions_eqv `{Univalence} (G : Group) : GSet G ≃ absGSet (abstr G).
Proof.
  refine (Eqv_comp (GSet_eqv G) _).
  pose (E := fun S : SetU => Eqv_comp (abstr_hom_eqv G (SG_S S))
                               (absHom_postcomp (abstr G) (SG_Perm_iso S))).
  exact (tot (fun S => fst (E S)); tot_isEquiv _ (fun S => snd (E S))).
Defined.

(** The underlying set of [ev(X)] is [X(sh_G)]. *)
Definition actions_eqv_set `{Univalence} (G : Group) (X : GSet G)
  : fst (fst (fst (actions_eqv G) X)) = el X (sh G)
  := refl.
