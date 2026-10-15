(** * Section 5.6 Any symmetry is a symmetry in Set

    Part of Chapter 5 ([actions.tex]); see [Actions.v] for an overview of
    the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - The homomorphism [ρ_G : Hom(G, Σ_{UG})] ([rho]), classified by
      [z ↦ (z = sh_G)] ([Brho0]).  The book points it by reflexivity; as
      the component structure is only propositionally equal, we point it
      by a path [rho_pt] whose underlying identification of sets is
      [refl] ([apF_rho_pt]).
    - On symmetries, [ρ_G(g)] is [x ↦ x g⁻¹] ([USym_rho_act]).
    - Theorem [lem:allgpsarepermutationgps] (Cayley): [ρ_G] is a
      monomorphism ([cayley]).  We use the elementary argument of the
      remark following the theorem: [g] is recovered from the action of
      [ρ_G(g)] on [refl_{sh_G}].

    Left out (time limit per result)
    - The proof via [lem:BGbytorsor], the description of the subgroup
      [E(G, ρ_G)], remark [rem:CayleyOversize] and exercise
      [xca:PP-fixed-permutations].
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core.
From SymmetryMirror Require Export Actions.S05_Torsors.

Local Open Scope uf_scope.

(** ** 5.6 Any symmetry is a symmetry in [Set] *)

Section Cayley.

  Context `{Univalence} (G : Group).

  Definition USymSet : SetU := (USym G; USym_isSet G).

  (** [Bρ_G :≡ P_(sh_G) : BG →* BΣ_{UG}], [z ↦ (z = sh_G)], pointed by
      [refl]. *)
  Definition Brho0 (z : utype (BG G)) : component SetU USymSet
    := (((z = sh G); BG_isGrpd G z (sh G));
        Trunc_functor (-1) (fun p : sh G = z => ap (fun y => ((y = sh G); BG_isGrpd G y (sh G)) : SetU) p)
          (snd (BG_isConn G) (sh G) z)).

  Definition rho_pt : ((USymSet; trunc refl) : component SetU USymSet) = Brho0 (sh G)
    := @path_sigma_prop SetU (fun S => ptrunc (USymSet = S)) (fun _ => ptrunc_isProp)
         (USymSet; trunc refl) (Brho0 (sh G)) refl.

  Definition rho : Hom G (SG_S USymSet) := @mkhom G (SG_S USymSet) (Brho0; rho_pt).

  Definition trp_paths_to (c : utype (BG G)) {z w : utype (BG G)} (g : z = w) (q : z = c)
    : trp (fun y => y = c) g q = q ⋅ g⁻¹.
  Proof. destruct g. exact (trans_1p q)^. Defined.

  Local Notation F := (fun S : component SetU USymSet => fst (fst S)).

  Definition apF_rho_pt : ap F rho_pt = refl
    := ap_compose fst fst rho_pt @ ap (ap fst) (ap_fst_pathpair refl _).

  Definition apF_USymf (g : USym G) : ap F (USymf rho g) = ap (fun z => z = sh G) g.
  Proof.
    change (ap F (rho_pt⁻¹ ⋅ (ap Brho0 g ⋅ rho_pt)) = ap (fun z => z = sh G) g).
    refine (ap_trans F _ _ @ _).
    refine (ap011 (fun a b => a ⋅ b) (ap_symm F rho_pt @ ap symm apF_rho_pt)
              (ap_trans F _ _ @ ap (fun a => _ ⋅ a) apF_rho_pt) @ _).
    refine (trans_1p _ @ _). exact (ap_compose Brho0 F g)^.
  Defined.

  (** On symmetries, [ρ_G(g)] acts on [UG] by [x ↦ x g⁻¹]. *)
  Definition USym_rho_act (g : USym G) (x : USym G)
    : trp F (USymf rho g) x = x ⋅ g⁻¹.
  Proof.
    refine (ptw (trp_ap idmap F (USymf rho g)) x @ _).
    refine (ap (fun r => trp idmap r x) (apF_USymf g) @ _).
    refine ((ptw (trp_ap idmap (fun z => z = sh G) g) x)^ @ _).
    exact (trp_paths_to (sh G) g x).
  Defined.

  (** Theorem [lem:allgpsarepermutationgps] (Cayley): [ρ_G] is a
      monomorphism. *)
  Definition cayley : ismono rho.
  Proof.
    refine (cancel_isInj (USym_isSet _) _). intros g g' e.
    pose (e' := (USym_rho_act g (refl (sh G)))^ @ ap (fun r : utype (loops (BG (SG_S USymSet))) => trp F r (refl (sh G))) e @ USym_rho_act g' (refl (sh G))).
    exact ((symm_symm g)^ @ ap symm e' @ symm_symm g').
  Defined.

End Cayley.
