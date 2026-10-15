(** * Section 7.7 Free groups

    Part of Chapter 7 ([congp.tex]); see [ConGroups.v] for an overview
    of the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Definition [def:bfree]: [BFGT S] as the library's coequalizer of
      the two maps [S → 1], with [fbase], [floop], and the induction
      principle [BFG_ind] (computing on [fbase] by [refl]); it is
      connected ([BFGT_isConn]).
    - Evaluation at the loops is an equivalence
      [(BF_S →* (B, b)) ≃ (S → (b = b))] for any pointed type
      ([free_ev_eqv]).
    - The free group [FG S], with generators [fgen], and its universal
      property [Hom(F_S, G) ≃ (S → UG)] ([FG_univ]).  Deviation: as for
      sums, [FG S] is classified by the [1]-truncation of [BF_S], since
      the book shows that [BF_S] is a groupoid only for decidable [S].

    Left out (time limit per result)
    - Signed letters, reduction and Dyck words, theorem
      [thm:free-group-elements] (reduced words), and the exercises
      [R_1 ≃ ℤ] and [F_{n+1} = F_n ∨ ℤ].
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core Colimits.Coeq.
From SymmetryMirror Require Export ConGroups.S06_Sums.

Local Open Scope uf_scope.

(** ** 7.7 Free groups *)

(** Definition [def:bfree]: the higher inductive type [BF_S] with a point
    [base] and loops [loop_s : base = base] for [s : S], implemented as
    the library's coequalizer of the two maps [S → 1]. *)
Section FreeGroup.

  Context (S : Type).

  Definition BFGT : Type := Coeq (fun _ : S => triv) (fun _ : S => triv).

  Definition fbase : BFGT := coeq triv.

  Definition floop (s : S) : fbase = fbase := cglue s.

  Definition BFG : Ustar := (BFGT; fbase).

  (** The induction principle, with its computation rules. *)
  Definition BFG_ind (A : BFGT -> Type) (a : A fbase)
    (l : forall s, PathOver A (floop s) a a) : forall x, A x
    := Coeq_ind A (fun t => match t with tt => a end) l.

  Definition BFG_ind_base (A : BFGT -> Type) (a : A fbase) l
    : BFG_ind A a l fbase = a := refl.

  Definition BFGT_isConn : isConn BFGT.
  Proof.
    refine (isConn_from_pt fbase _).
    exact (Coeq_ind (fun x => ptrunc (fbase = x)) (fun t => match t with tt => trunc refl end)
             (fun s => ptrunc_isProp _ _)).
  Defined.

  (** Evaluation [ev(k)(s) :≡ Ωk(loop_s)] is an equivalence
      [(BF_S →* (B, b)) ≃ (S → (b = b))], for any pointed type [(B, b)]. *)
  Definition free_ev {B : Type} {b : B} (k : BFG →* (B; b)) : S -> b = b
    := fun s => loops_fun k (floop s).

  Definition free_ve {B : Type} {b : B} (u : S -> b = b) : BFG →* (B; b)
    := (Coeq_rec B (fun _ => b) u; refl).

  Definition free_ev_ve `{Funext} {B : Type} {b : B} (u : S -> b = b)
    : free_ev (free_ve u) = u.
  Proof.
    apply ptw_inv. intro s. unfold free_ev, free_ve.
    refine (@loops_fun_refl BFG (B; b) (Coeq_rec B (fun _ => b) u) (floop s) @ _).
    exact (Coeq_rec_beta_cglue B _ u s).
  Defined.

  Definition free_ve_ev `{Funext} {B : Type} {b : B} (k : BFG →* (B; b))
    : free_ve (free_ev k) = k.
  Proof.
    destruct k as [k kp]. change (BFGT -> B) in k. revert b kp. refine (paths_ind_r _ _ _).
    refine (eqinv (snd (ptw_star (free_ve (free_ev ((k; refl) : BFG →* (B; k fbase))))
                                 ((k; refl) : BFG →* (B; k fbase)))) _).
    pose (u := free_ev ((k; refl) : BFG →* (B; k fbase))).
    simple refine (_; _).
    - refine (Coeq_ind (fun x => Coeq_rec B (fun _ => k fbase) u x = k x)
                (fun t => match t with tt => refl end) _).
      intro s. refine (transport_paths_FlFr (f := Coeq_rec B (fun _ => k fbase) u) (g := k) (cglue s) refl @ _).
      refine (ap (fun r => (r^ @ refl) @ ap k (cglue s)) (Coeq_rec_beta_cglue B _ u s) @ _).
      unfold u, free_ev. rewrite (@loops_fun_refl BFG (B; k fbase) k (floop s)).
      refine (ap (fun r => r @ _) (concat_p1 _) @ _). exact (concat_Vp _).
    - exact refl.
  Defined.

  Definition free_ev_eqv `{Funext} (B : Type) (b : B) : (BFG →* (B; b)) ≃ (S -> b = b)
    := mkEqv free_ev free_ve free_ve_ev free_ev_ve.

  (** The free group [F_S :≡ mkgroup(BF_S, base)].  The book proves that
      [BF_S] is a groupoid for decidable [S] (theorem
      [thm:free-group-elements]); as for sums, we take the
      [1]-truncation, which is a groupoid by construction. *)
  Definition FG : Group
    := mkgroup (Trunc 1 BFGT;
                (tr fbase;
                 (surj_isConn (f := tr)
                    (fun y => Trunc_ind (fun y => Ex (fun a => y = tr a))
                                (fun a => trunc (a; refl)) y)
                    BFGT_isConn;
                  IsTrunc_isGrpd (istrunc_truncation 1 _)))).

  (** The generators [ι_s : U F_S]. *)
  Definition fgen (s : S) : USym FG := ap tr (floop s).

  (** The universal property: [Hom(F_S, G) ≃ (S → UG)]. *)
  Definition FG_univ `{Funext} (G : Group) : Hom FG G ≃ (S -> USym G).
  Proof.
    refine (Eqv_comp (Copy_eqv _) _).
    refine (Eqv_comp (Eqv_of_Equiv (equiv_functor_sigma_pb
               (Q := fun k : BFGT -> utype (BG G) => sh G = k fbase)
               (Equiv_of_Eqv (@trunc_univ_prop _ 1 BFGT (utype (BG G))
                                (isGrpd_IsTrunc (BG_isGrpd G)))))) _).
    exact (free_ev_eqv (utype (BG G)) (sh G)).
  Defined.

End FreeGroup.
