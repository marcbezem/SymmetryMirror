(** * Section 8.4 The pullback

    Part of Chapter 8 ([congp.tex]); see [ConGroups.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Definition [def:pullback], exercise [xca:univpropofpullback] and
      the example of the preimage: formalized in Section 6.8
      ([Cats/S08_Limits.v]), since [cats.tex] repeats them (with the same
      labels; NOTE for the book text).
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

(** ** 8.4 The pullback *)

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
