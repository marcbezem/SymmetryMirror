(** * Section 5.3 Subgroups

    Part of Chapter 5 ([actions.tex]); see [Actions.v] for an overview of
    the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Definition [def:set-of-subgroups]: [SubGrp G :≡ ∑_X X(sh_G) ×
      isTrans(X)]; exercise [xca:group-Xx!] ([TotG_isGrpd] and
      [conn_of_trans] of Section 5.2); definition
      [def:underlying-group-of-subgroup] ([subgrp_group]).
    - Lemma [lem:SubGisset] ([SubGrp_isSet]), via
      [pointed_GSet_paths_isProp]: identifications of pointed transitive
      [G]-sets form the fibers of the injective evaluation map
      ([ev_path_isInj]).
    - Definition [def:decidable-subgroup] ([isDecSubGrp]).
    - Definition [def:typeofmono]: [ismono], [Mono G], [Mono_trivial],
      [Mono_proper]; example [ex:prodinclismono] ([inG1_ismono],
      [inG2_ismono]).
    - The map [F : Sub(G) → Mono(G)] of lemma [lem:SubG=MonoG]
      ([subgrp_to_mono]); [Ufst] is injective since identifications in
      a total space over a family of sets are determined by their first
      component ([ap_fst_cancel]).
    - Lemma [lem:E-preserves-symms] ([E_preserves_symms]), stated for
      [F(X, pt)] (the book reduces to this case).
    - Definition [def:triv-proper-Mono] ([SubGrp_trivial],
      [SubGrp_proper]).
    - Constructions [con:lagrange] ([lagrange]) and [cor:lagrange-dep-sum]
      ([lagrange_dep]).
    - Exercise [xca:lagrange] ([subgrp_Finite], [lagrange_card]), with
      the library's [Finite] and [fcard]; the choice function needed by
      the Lagrange construction exists merely, by transitivity and finite
      choice.

    Left out (time limit per result)
    - That [F] is an equivalence (lemma [lem:SubG=MonoG], exercise
      [xca:SubG=MonoG]) and corollary [lem:setofsubgroups]; this needs
      the object classifier [(∑_A (A → BG)) ≃ (BG → U)] restricted to
      connected domains and set-valued fibers.
    - Examples [ex:Rm0-subgroup], [exa:fix1subSGn], [exa:C3subC6],
      [ex:SGninSGn+1], [exa:EforSG3], [ex:prodinclisGset], and exercises
      [xca:n-is-ptd-n+1], [xca:A-is-A-1+1], [xca:SG2subSG3],
      [xca:C3subSG3], [xca:lagrange-Z-action-Rm],
      [xca:lagrange-if-subgr-not-normal].
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core Cubical.DPath HFiber
  Spaces.Finite.Fin Spaces.Finite.Finite Spaces.Nat.Core Projective.
From SymmetryMirror Require Export Actions.S02_GSets.

Local Open Scope uf_scope.

(** ** 5.3 Subgroups *)

(** Definition [def:set-of-subgroups]. *)
Definition SubGrp (G : Group) : Type
  := {X : GSet G & el X (sh G) × istrans X}.

Definition sg_X {G : Group} (S : SubGrp G) : GSet G := fst S.
Definition sg_pt {G : Group} (S : SubGrp G) : el (sg_X S) (sh G) := fst (snd S).
Definition sg_trans {G : Group} (S : SubGrp G) : istrans (sg_X S) := snd (snd S).

(** Exercise [xca:group-Xx!]. *)
Definition TotG_isGrpd `{Funext} {G : Group} (X : GSet G) : isGrpd (TotG X)
  := Sigma_ntype 1 (BG_isGrpd G) (fun z => set_ntype 1 (el_isSet X z)).

(** Definition [def:underlying-group-of-subgroup]. *)
Definition subgrp_group `{Funext} {G : Group} (S : SubGrp G) : Group
  := mkgroup (TotG (sg_X S); ((sh G; sg_pt S);
                (conn_of_trans _ (sg_trans S); TotG_isGrpd (sg_X S)))).

(** Lemma [lem:SubGisset]. *)
Definition istrans_isProp {G : Group} (X : GSet G) : isProp (istrans X) := ptrunc_isProp.

Definition trp_el_hom_of_path {G : Group} {X Y : GSet G} (e : X = Y) (z : utype (BG G))
  (x : el X z) : trp (fun X : GSet G => el X z) e x = hom_of_path e z x.
Proof. destruct e. exact refl. Defined.

Definition pointed_GSet_paths_isProp `{Univalence} {G : Group} (X X' : GSet G)
  (t : istrans X) (x : el X (sh G)) (x' : el X' (sh G))
  : isProp (((X; x) : {X : GSet G & el X (sh G)}) = (X'; x')).
Proof.
  refine (isProp_Eqv (path_sigma_eqv (Y := fun X : GSet G => el X (sh G))) _).
  refine (isProp_Eqv _ (ev_path_isInj (Y := X') t x x')).
  refine (tot (fun e (h : x' = hom_of_path e (sh G) x) =>
                 (h⁻¹ ⋅ trp_el_hom_of_path e (sh G) x) : PathOver _ e x x');
          tot_isEquiv _ (fun e => _)).
  destruct e. change (isEquiv (fun h : x' = x => h⁻¹ ⋅ refl)).
  refine (iso_to_isEquiv _ (fun k => k⁻¹) _ _); intro h; destruct h; exact refl.
Defined.

Definition SubGrp_isSet `{Univalence} (G : Group) : isSet (SubGrp G).
Proof.
  pose (r := mkEqv (fun S : SubGrp G => (((sg_X S; sg_pt S) : {X : GSet G & el X (sh G)});
                                          sg_trans S))
                   (fun w : {Y : {X : GSet G & el X (sh G)} & istrans (fst Y)} =>
                      (fst (fst w); (snd (fst w); snd w)) : SubGrp G)
                   (fun _ => refl) (fun _ => refl)
             : SubGrp G ≃ {Y : {X : GSet G & el X (sh G)} & istrans (fst Y)}).
  intros u v.
  refine (isProp_Eqv (Eqv_inv (Eqv_comp (Eqv_of_Equiv (equiv_ap' (Equiv_of_Eqv r) u v))
                                 (subtype_paths_eqv (fun Y => istrans_isProp (fst Y)) _ _))) _).
  exact (pointed_GSet_paths_isProp _ _ (sg_trans u) _ _).
Defined.

(** Definition [def:decidable-subgroup]. *)
Definition isDecSubGrp {G : Group} (S : SubGrp G) : Type := isDecSet (el (sg_X S) (sh G)).

(** Definition [def:typeofmono]. *)
Definition ismono {H G : Group} (i : Hom H G) : Type := isInj (USymf i).

Definition Mono (G : Group) : Type := {H : Group & {i : Hom H G & ismono i}}.

Definition Mono_trivial {G : Group} (m : Mono G) : Type := isContr (utype (BG (fst m))).

Definition Mono_proper {G : Group} (m : Mono G) : Type := ¬ isIso (fst (snd m)).

(** Example [ex:prodinclismono]: the inclusions into [G × H] are
    monomorphisms. *)
Definition inj_of_retraction {A B : Type} (sB : isSet B) (f : A -> B) (r : B -> A)
  (h : forall a, r (f a) = a) : isInj f
  := cancel_isInj sB (fun a a' e => (h a)^ @ ap r e @ h a').

Definition ap_fst_ap_pair {A B : Type} (b : B) {x y : A} (p : x = y)
  : ap fst (ap (fun z => (z; b) : A × B) p) = p.
Proof. destruct p. exact refl. Defined.

Definition ap_snd_ap_pair {A B : Type} (a : A) {x y : B} (p : x = y)
  : ap (fun w : A × B => snd w) (ap (fun z => (a; z) : A × B) p) = p.
Proof. destruct p. exact refl. Defined.

Definition inG1_ismono `{Funext} (G K : Group) : ismono (inG1 G K)
  := inj_of_retraction (USym_isSet _) _ (fun q : USym (prodG G K) => ap fst q)
       (fun g => ap (ap fst) (trans_1p _) @ ap_fst_ap_pair _ g).

Definition inG2_ismono `{Funext} (G K : Group) : ismono (inG2 G K)
  := inj_of_retraction (USym_isSet _) _ (fun q : USym (prodG G K) => ap (fun w : utype (BG (prodG G K)) => snd w) q)
       (fun g => ap (ap (fun w : utype (BG (prodG G K)) => snd w)) (trans_1p _) @ ap_snd_ap_pair _ g).

(** Over a family of sets, identifications in the total type are
    determined by their first component. *)
Definition ap_fst_cancel {A : Type} {Y : A -> Type} (sY : forall a, isSet (Y a))
  {u v : {a : A & Y a}} (h h' : u = v) (e : ap fst h = ap fst h') : h = h'.
Proof.
  refine ((pathpair_pathsplit h)^ @ _ @ pathpair_pathsplit h').
  pose (hP := fun p : fst u = fst v => sY _ (trp Y p (snd u)) (snd v)
              : isProp (PathOver Y p (snd u) (snd v))).
  refine (ap (fun w : {p : fst u = fst v & PathOver Y p (snd u) (snd v)} =>
                pathpair (fst w) (snd w))
             (path_sigma_prop hP (u := pathsplit h) (v := pathsplit h') _)).
  exact (fst_pathsplit h @ e @ (fst_pathsplit h')^).
Defined.

(** The map [F : Sub(G) → Mono(G)] of lemma [lem:SubG=MonoG]. *)
Section SubToMono.

  Context `{Funext} {G : Group} (S : SubGrp G).

  Definition subgrp_incl : Hom (subgrp_group S) G
    := @mkhom (subgrp_group S) G ((fun w => fst w); refl).

  Definition subgrp_incl_ismono : ismono subgrp_incl.
  Proof.
    refine (cancel_isInj (USym_isSet G) _). intros h h' e.
    refine (ap_fst_cancel (el_isSet (sg_X S)) h h' _).
    exact ((trans_1p _)^ @ e @ trans_1p _).
  Defined.

  Definition subgrp_to_mono : Mono G := (subgrp_group S; (subgrp_incl; subgrp_incl_ismono)).

  Definition ap_fst_tot_path_act {z w : utype (BG G)} (p : z = w) (a : el (sg_X S) z)
    : ap fst (tot_path_act (sg_X S) p a) = p.
  Proof. destruct p. exact refl. Defined.

  Definition ap_fst_act_path {z w : utype (BG G)} (p : z = w) (a : el (sg_X S) z)
    (b : el (sg_X S) w) (e : act (sg_X S) p a = b)
    : ap fst (ap (fun c => (w; c) : TotG (sg_X S)) e ⋅ tot_path_act (sg_X S) p a) = p.
  Proof. destruct e. exact (ap_fst_tot_path_act p a). Defined.

  (** Lemma [lem:E-preserves-symms], for [F(X, pt)]. *)
  Definition E_preserves_symms (g : USym G)
    : (act (sg_X S) g (sg_pt S) = sg_pt S)
      <-> Ex (fun h : USym (subgrp_group S) => g = USymf subgrp_incl h).
  Proof.
    split.
    - intro e. apply trunc.
      refine (ap (fun c => (sh G; c) : TotG (sg_X S)) e ⋅ tot_path_act _ g (sg_pt S); _).
      refine (_ @ (trans_1p _)^).
      change (g = ap fst (ap (fun c => (sh G; c) : TotG (sg_X S)) e
                          ⋅ tot_path_act (sg_X S) g (sg_pt S))).
      exact (ap_fst_act_path g _ _ e)^.
    - intro h. refine (ptrunc_rec (el_isSet _ _ _ _) _ h). intros [k e].
      refine (ap (fun r => act (sg_X S) r (sg_pt S)) (e @ trans_1p _) @ _).
      exact (act_ap_fst (sg_X S) k).
  Defined.

End SubToMono.

(** Definition [def:triv-proper-Mono]. *)
Definition SubGrp_trivial {G : Group} (S : SubGrp G) : Type := isContr (TotG (sg_X S)).

Definition SubGrp_proper {G : Group} (S : SubGrp G) : Type
  := ¬ isContr (el (sg_X S) (sh G)).

(** ** 5.3.3 The Lagrange construction *)
Section Lagrange.

  Context `{Funext} {G : Group} (S : SubGrp G).

  Local Notation X := (sg_X S).
  Local Notation pt0 := (sg_pt S).

  Definition cls (g : USym G) : el X (sh G) := act X g pt0.

  Definition fiber_cls_eqv (x : el X (sh G))
    : fiber cls x ≃ (((sh G; pt0) : TotG X) = (sh G; x)).
  Proof.
    refine (Eqv_comp _ (path_sigma_eqv (Y := el X))).
    refine (tot (fun g (e : x = cls g) => e⁻¹ : PathOver (el X) g pt0 x);
            tot_isEquiv _ (fun g => _)).
    refine (iso_to_isEquiv _ (fun e => e⁻¹) _ _); intro e; exact (symm_symm e).
  Defined.

  Definition back_path (x : el X (sh G)) (f : {g : USym G & act X g x = pt0})
    : ((sh G; x) : TotG X) = (sh G; pt0)
    := ap (fun c => (sh G; c) : TotG X) (snd f) ⋅ tot_path_act X (fst f) x.

  (** Construction [con:lagrange]. *)
  Definition lagrange (f : forall x : el X (sh G), {g : USym G & act X g x = pt0})
    : USym G ≃ (el X (sh G) × USym (subgrp_group S)).
  Proof.
    refine (Eqv_comp (Eqv_inv (sum_of_fibers cls)) _).
    refine (tot (fun x (u : fiber cls x) => back_path x (f x) ⋅ fst (fiber_cls_eqv x) u);
            tot_isEquiv _ (fun x => _)).
    exact (comp_isEquiv (snd (fiber_cls_eqv x)) (comp_l_isEquiv (back_path x (f x)))).
  Defined.

  (** Construction [cor:lagrange-dep-sum]. *)
  Definition lagrange_dep (f : forall x : el X (sh G), {g : USym G & act X g x = pt0})
    : USym G ≃ {x : el X (sh G) & ((sh G; x) : TotG X) = (sh G; x)}.
  Proof.
    refine (Eqv_comp (Eqv_inv (sum_of_fibers cls)) _).
    refine (tot (fun x (u : fiber cls x) => fst (fiber_cls_eqv x) u ⋅ back_path x (f x));
            tot_isEquiv _ (fun x => _)).
    refine (comp_isEquiv (snd (fiber_cls_eqv x)) _).
    refine (iso_to_isEquiv _ (fun q => q ⋅ (back_path x (f x))⁻¹) _ _); intro q.
    - refine ((trans_assoc _ _ _)^ @ _).
      exact (ap (fun r => q ⋅ r) (trans_Vp _) @ trans_1p q).
    - refine ((trans_assoc _ _ _)^ @ _).
      exact (ap (fun r => q ⋅ r) (trans_pV _) @ trans_1p q).
  Defined.

End Lagrange.

(** Exercise [xca:lagrange]: for a finite group [G] and a finite [G]-set,
    the underlying group [H] of [(X, pt)] is finite and
    [Card(G) = Card(X) · Card(H)].  We count with the library's [fcard]. *)
Section LagrangeCount.

  Context `{Funext} {G : Group} (S : SubGrp G).

  Local Notation X := (sg_X S).
  Local Notation pt0 := (sg_pt S).

  Definition lagrange_choice (x : el X (sh G))
    : ptrunc {g : USym G & act X g x = pt0}
    := Trunc_functor (-1) (fun r => (ap fst r; act_ap_fst X r))
         (snd (conn_of_trans X (sg_trans S)) (sh G; x) (sh G; pt0)).

  Context (FG : Finite (USym G)) (FX : Finite (el X (sh G))).

  Definition merely_lagrange : ptrunc (USym G ≃ (el X (sh G) × USym (subgrp_group S)))
    := Trunc_functor (-1) (lagrange S)
         (@finite_choice _ FX (fun x => {g : USym G & act X g x = pt0}) (fun _ => tt)
            lagrange_choice).

  Definition subgrp_Finite : Finite (USym (subgrp_group S)).
  Proof.
    refine (ptrunc_rec IsHProp_isProp _ merely_lagrange). intro e.
    pose (FP := finite_equiv' _ (Equiv_of_Eqv e) FG).
    exact (finite_equiv' _ (hfiber_fibration pt0 (fun _ => USym (subgrp_group S)))^-1
             (finite_hfiber (fun w : el X (sh G) × USym (subgrp_group S) => fst w) pt0)).
  Defined.

  Definition lagrange_card
    : fcard (USym G) = (fcard (el X (sh G)) * @fcard _ subgrp_Finite)%nat.
  Proof.
    refine (ptrunc_rec (ℕ_isSet _ _) _ merely_lagrange). intro e.
    pose (FH := subgrp_Finite).
    refine (fcard_equiv' (Equiv_of_Eqv (Eqv_comp e (binprod_prod _ _))) @ _).
    exact (fcard_prod _ _).
  Defined.

End LagrangeCount.
