(** * Section 7.4 The pullback

    Part of Chapter 7 ([congp.tex]); see [ConGroups.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Definition [def:pullback] ([pullback], [prB], [prC]).
    - Exercise [xca:univpropofpullback] ([pullback_univ_map],
      [pullback_univ_isEquiv]); the book's formula [(f(a), g(a), p(a))]
      should read [(β(a), γ(a), p(a))].  NOTE for the book text.
    - Example: the preimage as a pullback ([pullback_point_eqv]).
    - Definition [def:intersectionand unionofsets] ([sub_inter],
      [sub_union]); the book's union [A(s) + B(s)] is not a family of
      propositions, so we truncate it.  NOTE for the book text.
      Exercise [xca:intersectionpullbackofsets](1)
      ([pullback_inter_eqv]).
    - Definition [def:intersectionofgroups]: [pullbackG f f'] (the
      component at [(sh_H, sh_{H'}, p_{f'} p_f⁻¹)]), with its projections,
      and [intersectionG] of two monomorphisms.

    Left out (time limit per result)
    - Example [ex:pullbackandgcd], the example [L ℤ = a ℤ ∩ b ℤ], exercise
      [xca:intersectionpullbackofsets](2) (cardinalities), and the
      exercise on [Hom(K, H ×_G H')] and [U(H ×_G H')].
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core.
From SymmetryMirror Require Export ConGroups.S03_Wreath.

Local Open Scope uf_scope.

(** ** 7.4 The pullback *)

(** Definition [def:pullback]: [∏(f,g) :≡ ∑_{(b,c):B×C} (f(b) = g(c))]. *)
Definition pullback {B C D : Type} (f : B -> D) (g : C -> D) : Type
  := {bc : B × C & f (fst bc) = g (snd bc)}.

Definition prB {B C D : Type} {f : B -> D} {g : C -> D} (w : pullback f g) : B
  := fst (fst w).

Definition prC {B C D : Type} {f : B -> D} {g : C -> D} (w : pullback f g) : C
  := snd (fst w).

(** Exercise [xca:univpropofpullback]. *)
Definition pullback_univ_map {A B C D : Type} (f : B -> D) (g : C -> D)
  (w : pullback (fun β : A -> B => f ∘ β) (fun γ : A -> C => g ∘ γ))
  : A -> pullback f g
  := fun a => ((fst (fst w) a; snd (fst w) a); ptw (snd w) a).

Definition pullback_univ_isEquiv `{Funext} {A B C D : Type} (f : B -> D) (g : C -> D)
  : isEquiv (@pullback_univ_map A B C D f g).
Proof.
  refine (iso_to_isEquiv _
            (fun h => (((fun a => prB (h a)); (fun a => prC (h a)));
                       ptw_inv (fun a => snd (h a)))) _ _).
  - intros [[β γ] p]. cbn.
    exact (ap (fun q => (((β; γ) : (A -> B) × (A -> C)); q)) (eqinv_l (funext _ _) p)).
  - intro h. apply ptw_inv. intro a. unfold pullback_univ_map. cbn.
    exact (ap (fun q => (((prB (h a); prC (h a)) : B × C); q))
              (ptw (eqinv_r (funext _ _) (fun a => snd (h a))) a)).
Defined.

(** Example: the preimage as a pullback, [B ×_D 1 ≃ f⁻¹(d)]. *)
Definition pullback_point_eqv {B D : Type} (f : B -> D) (d : D)
  : pullback f (fun _ : True => d) ≃ fiber f d.
Proof.
  refine (mkEqv (fun w => (prB w; (snd w)⁻¹))
                (fun v => (((fst v; triv) : B × True); (snd v)⁻¹)) _ _).
  - intros [[b []] p]. exact (ap (fun q => (((b; triv) : B × True); q)) (symm_symm p)).
  - intros [b p]. exact (ap (fun q => (b; q)) (symm_symm p)).
Defined.

(** Definition [def:intersectionand unionofsets]: intersection and union
    of subsets (the union is the propositional truncation of the sum, so
    that it is again a subset). *)
Definition sub_inter {S : Type} (P Q : Sub S) : Sub S
  := fun s => ((fst (P s) × fst (Q s)); prod_isProp (snd (P s)) (snd (Q s))).

Definition sub_union {S : Type} (P Q : Sub S) : Sub S
  := fun s => ptrunc_PropU (fst (P s) ⨿ fst (Q s)).

(** Exercise [xca:intersectionpullbackofsets](1). *)
Definition pullback_inter_eqv {S : Type} (P Q : Sub S)
  : pullback (fun x : carrier P => fst x) (fun y : carrier Q => fst y)
    ≃ carrier (sub_inter P Q).
Proof.
  refine (mkEqv
    (fun w : pullback (fun x : carrier P => fst x) (fun y : carrier Q => fst y) =>
       exist (fun s => fst (sub_inter P Q s)) (fst (prB w))
         ((snd (prB w); trp (fun s => fst (Q s)) (snd w)⁻¹ (snd (prC w)))
          : fst (P (fst (prB w))) × fst (Q (fst (prB w)))))
    (fun v : carrier (sub_inter P Q) =>
       (((((fst v; fst (snd v)) : carrier P); ((fst v; snd (snd v)) : carrier Q))
         : carrier P × carrier Q); refl))
    _ _).
  - intros [[[s x] [s' y]] p]. cbn in p. destruct p. exact refl.
  - intros [s [x y]]. exact refl.
Defined.

(** Definition [def:intersectionofgroups]: the pullback of groups, the
    component of [BH ×_{BG} BH'] at [(sh_H, sh_{H'}, p_{f'} p_f⁻¹)]. *)
Section PullbackGroups.

  Context `{fe : Funext} {H H' G : Group} (f : Hom H G) (f' : Hom H' G).

  Definition pullbackB : Type := pullback (fst (Bf f)) (fst (Bf f')).

  Definition pullbackB_isGrpd : isGrpd pullbackB
    := Sigma_isGrpd (Sigma_isGrpd (BG_isGrpd H) (fun _ => BG_isGrpd H'))
         (fun _ => set_isGrpd (BG_isGrpd G _ _)).

  Definition pullbackB_pt : pullbackB
    := (((sh H; sh H') : utype (BG H) × utype (BG H')); snd (Bf f') ⋅ (snd (Bf f))⁻¹).

  Definition pullbackG : Group := AutG pullbackB_isGrpd pullbackB_pt.

  (** The projections are homomorphisms. *)
  Definition pullbackG_pr1 : Hom pullbackG H
    := mkhom (((fun w : component pullbackB pullbackB_pt => prB (fst w)); refl)
                : BG pullbackG →* BG H).

  Definition pullbackG_pr2 : Hom pullbackG H'
    := mkhom (((fun w : component pullbackB pullbackB_pt => prC (fst w)); refl)
                : BG pullbackG →* BG H').

End PullbackGroups.

(** The intersection of two monomorphisms is their pullback. *)
Definition intersectionG `{Funext} {G : Group} (m m' : Mono G) : Group
  := pullbackG (fst (snd m)) (fst (snd m')).
