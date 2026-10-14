(** * Section 3.6 Connected coverings over the circle

    Part of Chapter 3 ([circle.tex]); see [Circle.v] for an overview of
    the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - Iteration [t^n] for [n : ℤ] of a permutation of a set ([tpow]),
      with [t^{n+m} = t^m t^n] and [t^{-n} t^n = id].
    - [def:connected-by-t]: [conn_by], an equivalence relation.
    - [con:cycset-connS1cover]: [‖∑_{z:S1} E(z)‖₀ ≃ X/∼] ([quot_eqv]) for
      [E :≡ ve_U(X, etop t)].
    - [def:Cyc], and [thm:cycset-connS1cover]: [∑_z E(z)] is connected iff
      [(X,t)] is a cycle ([conn_isCycle], [isCycle_conn]).
    - [def:dgm-map] ([dg]).
    - The standard finite [m]-element cycle with the exercise: the
      successor on [∑_i (i < m)] with an explicit inverse, transported to
      [Fin m] ([finsuccEqv]); [def:RmtoS1] ([Rm], [powm]), a covering.
    - Exercise [xca:preim-eq] ([preim_eq]).
    - [def:subgroup-zet-of-cycle] ([Ht]) and [lem:cycle-order-point-ap]:
      [H_t = {n | t^n(x) = x}] for a cycle ([Ht_point]); the equivalence
      [((base,x) = (base,x)) ≃ ∑_n (t^n(x) = x)] whose first component is
      the winding number of the projected loop ([loopsAE_isEquiv]); and
      [H_t] is the image of that map ([image_loops_Ht]).

    Left out (not yet formalized)
    - [con:psi-alpha-m] and [cor:dgm-conncov] (the book leaves the
      inverse of [ψ_m] as an exercise).
    - [lem:IdCycle], [cor:ConnCycles], [cor:id-m-cycle],
      [cor:set-trunc-cyc], [xca:map-of-cycles], [def:Order],
      [def:standard-cycle], the Limited Principle of Omniscience with
      [LEM → LPO] and [xca:not-not-lpoP], [lem:componentsofcoversofS1]
      and [rem:flipthecircle]. *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Types.Arrow Truncations.Core Colimits.Coeq
  Colimits.Pushout Spaces.Nat.Core Spaces.Int Spaces.Circle
  Spaces.Finite.Fin Spaces.Finite.FinNat.
From SymmetryMirror Require Export Circle.S05_Reinterpretation.

Local Open Scope uf_scope.

(** ** 3.6 Connected coverings over the circle *)

(** Iteration [t^n] of a permutation [t] of a set, for [n : ℤ]. *)
Section Iteration.

  Context `{Funext} {X : Type} (sX : isSet X) (t : X ≃ X).

  Definition tpow (n : ℤ) (x : X) : X := iterZ t n x.

  Definition tpow_zs (n : ℤ) (x : X) : tpow (zs n) x = fst t (tpow n x)
    := iterZ_zs sX t n x.

  Definition tpow_zp (n : ℤ) (x : X) : tpow (zp n) x = eqinv (snd t) (tpow n x)
    := (eqinv_l (snd t) _)^
       @ ap (eqinv (snd t)) ((tpow_zs (zp n) x)^ @ ap (fun k => tpow k x) (zs_zp n)).

  Definition tpow_add (n m : ℤ) (x : X) : tpow (zadd n m) x = tpow m (tpow n x).
  Proof.
    revert m. refine (ℤ_ind_prop _ (fun m => sX _ _) _ _).
    - intro k. induction k as [|k IH].
      + exact refl.
      + exact (tpow_zs (zadd n (iplus k)) x @ ap (fst t) IH).
    - intros [k]. induction k as [|k IH].
      + exact refl.
      + exact (ap (fun w => tpow w x) (eqinv_mkEqv zs zp zp_zs zs_zp _)
               @ tpow_zp _ x @ ap (eqinv (snd t)) IH).
  Defined.

  Definition zadd_zneg (n : ℤ) : zadd n (zneg n) = iplus 0
    := toInt_inj (y := iplus 0) (toInt_zadd _ _ @ ap (int_add (toInt n)) (toInt_zneg n)
                  @ int_add_neg_r _).

  Definition tpow_neg (n : ℤ) (x : X) : tpow (zneg n) (tpow n x) = x
    := (tpow_add n (zneg n) x)^ @ ap (fun k => tpow k x) (zadd_zneg n).

  (** Definition [def:connected-by-t]: [x ∼ x'] iff [x' = t^n(x)] for some
      [n : ℤ]; an equivalence relation. *)
  Definition conn_by (x x' : X) : PropU
    := (ptrunc {n : ℤ & x' = tpow n x}; ptrunc_isProp).

  Definition conn_by_refl (x : X) : fst (conn_by x x) := trunc (iplus 0; refl).

  Definition conn_by_sym (x x' : X) : fst (conn_by x x') -> fst (conn_by x' x)
    := ptrunc_rec ptrunc_isProp
         (fun w => trunc (zneg (fst w); (tpow_neg (fst w) x)^ @ ap (tpow (zneg (fst w))) (snd w)^)).

  Definition conn_by_trans (x x' x'' : X)
    : fst (conn_by x x') -> fst (conn_by x' x'') -> fst (conn_by x x'')
    := fun u v => ptrunc_rec ptrunc_isProp (fun w => ptrunc_rec ptrunc_isProp
         (fun w' => trunc (zadd (fst w) (fst w');
                           snd w' @ ap (tpow (fst w')) (snd w) @ (tpow_add _ _ x)^)) v) u.

End Iteration.

(** Construction [con:cycset-connS1cover]. *)
Section CycsetConnS1cover.

  Context `{Univalence} {X : Type} (sX : isSet X) (t : X ≃ X).

  Definition E : S1 -> Type := ve Type (X; etop t).

  Definition trp_E_loop (y : X) : trp E loop y = fst t y.
  Proof.
    refine (transport_compose idmap E loop y @ _).
    refine (ap (fun r => transport idmap r y) (S1_rec_loop Type X (etop t)) @ _).
    exact (ptw (ap fst (ptoe_etop t)) y).
  Defined.

  Definition trp_E_loopV (y : X) : trp E loop⁻¹ y = eqinv (snd t) y
    := (eqinv_l (snd t) _)^ @ ap (eqinv (snd t)) ((trp_E_loop _)^ @ transport_pV E loop y).

  Definition AE : Type := {z : S1 & E z}.

  Definition step (y : X) : ((base; y) : AE) = (base; fst t y)
    := pathpair (Y := E) loop (trp_E_loop y).

  Definition conn_orbit (n : ℤ)
    : forall x : X, ptrunc (((base; x) : AE) = (base; tpow t n x)).
  Proof.
    revert n. refine (ℤ_ind_prop _ (fun n => Pi_isProp (fun _ => ptrunc_isProp)) _ _).
    - intros k x. induction k as [|k IH].
      + exact (trunc refl).
      + exact (ptrunc_rec ptrunc_isProp (fun p => trunc (step _ ⋅ p)) IH).
    - intros [k] x. induction k as [|k IH].
      + exact (trunc refl).
      + refine (ptrunc_rec ptrunc_isProp (fun p => trunc (_ ⋅ p)) IH).
        exact (step (eqinv (snd t) _) @ ap (fun v => (base; v) : AE) (eqinv_r (snd t) _))^.
  Defined.

  Let R := conn_by t.

  Definition Q : Type := quot R.

  Definition g0_loop : PathOver (fun z => E z -> Q) loop (cls R) (cls R).
  Proof.
    apply ptw_inv. intro y.
    refine (transport_arrow_toconst loop (cls R) y @ _).
    refine (ap (cls R) (trp_E_loopV y) @ _).
    apply (snd (cls_eq_iff R (conn_by_refl t) (conn_by_sym sX t) (conn_by_trans sX t) _ _)).
    exact (trunc (iplus 1; (eqinv_r (snd t) y)^)).
  Defined.

  Definition g0 : forall z : S1, E z -> Q := S1_ind (fun z => E z -> Q) (cls R) g0_loop.

  Definition gq : strunc AE -> Q
    := strunc_rec (quot_isSet R) (fun w => g0 (fst w) (snd w)).

  Definition hq_resp (x x' : X) (r : fst (R x x'))
    : settrunc ((base; x) : AE) = settrunc (base; x').
  Proof.
    refine (ptrunc_rec (strunc_isSet _ _) _ r). intros [n e].
    refine (ptrunc_rec (strunc_isSet _ _) _ (conn_orbit n x)). intro p.
    exact (ap settrunc ((ap (fun v => (base; v) : AE) e)⁻¹ ⋅ p)).
  Defined.

  Definition hq : Q -> strunc AE
    := fbar R (conn_by_refl t) strunc_isSet (fun x : X => settrunc ((base; x) : AE)) hq_resp.

  Definition quot_eqv : strunc AE ≃ Q.
  Proof.
    refine (mkEqv gq hq _ _).
    - refine (strunc_ind_prop _ (fun s => strunc_isSet _ _) _). intros [z e]. revert z e.
      refine (S1_ind_prop (fun z => forall e : E z, hq (gq (settrunc (z; e))) = settrunc (z; e))
                (fun z => Pi_isProp (fun e => strunc_isSet _ _)) _).
      intro e. exact refl.
    - refine (im_ind R _ (fun q => quot_isSet R _ _) _). intro x. exact refl.
  Defined.

  (** Corollary [thm:cycset-connS1cover]: the covering [(∑_{z:S1} E(z), fst)]
      is connected iff [(X,t)] is a cycle, i.e. [X] is nonempty and any
      two elements are connected by [t]. *)
  Definition isCycle : Type := ptrunc X × (forall x x' : X, fst (R x x')).

  Definition conn_isCycle (c : isConn AE) : isCycle.
  Proof.
    pose (cQ := isContr_Eqv quot_eqv (isConn_strunc_isContr c)).
    refine (_; fun x x' => fst (cls_eq_iff R (conn_by_refl t) (conn_by_sym sX t)
                                  (conn_by_trans sX t) x x') (isContr_isProp' cQ _ _)).
    exact (ptrunc_rec ptrunc_isProp (fun w => trunc (fst w)) (snd (fst cQ))).
  Defined.

  Definition isCycle_conn (cy : isCycle) : isConn AE.
  Proof.
    apply strunc_isContr_isConn.
    refine (isContr_Eqv (Eqv_inv quot_eqv) _).
    refine (ptrunc_rec (isContr_isProp _) _ (fst cy)). intro x0.
    refine (cls R x0; im_ind R _ (fun q => quot_isSet R _ _) _). intro x.
    exact (snd (cls_eq_iff R (conn_by_refl t) (conn_by_sym sX t) (conn_by_trans sX t) _ _)
             (snd cy x0 x)).
  Defined.

End CycsetConnS1cover.

(** Definition [def:Cyc]. *)
Definition Cyc `{Funext} : Type
  := {X : SetU & {t : fst X ≃ fst X &
       ptrunc (fst X) × (forall x x' : fst X, fst (conn_by t x x'))}}.

(** Definition [def:dgm-map]: the degree [m] function, [dg_m(loop) := loop^m]. *)
Definition dg `{Univalence} (m : ℕ) : S1 -> S1 := S1_rec S1 base (loopZ (iplus m)).

(** The standard finite [m]-element cycle, for [m = k+1]: the successor
    [zs(i) :≡ i+1] for [i < m-1] and [zs(m-1) :≡ 0], defined on
    [∑_{i:ℕ} (i < m)] (the library's [FinNat]) and transported to [Fin m]
    along [Fin m ≃ ∑_i (i < m)].  The exercise asks for an explicit
    inverse. *)
Section FinCycle.

  Context (k : ℕ).

  Definition fn_isProp_lt (x : ℕ) : isProp (x < S k)%nat := IsHProp_isProp.

  Definition fs (u : FinNat (S k)) : FinNat (S k)
    := match dec (fst u < k)%nat with
       | inl l => (S (fst u); leq_succ l)
       | inr _ => (0%nat; leq_succ (leq_zero_l k))
       end.

  Definition fp (u : FinNat (S k)) : FinNat (S k)
    := match u with
       | (O; _) => (k; leq_refl (S k))
       | (S x; l) => (x; leq_succ_l l)
       end.

  Definition fs_fp (u : FinNat (S k)) : fs (fp u) = u.
  Proof.
    destruct u as [[|x] l]; unfold fs, fp; cbn.
    - destruct (dec (k < k)%nat) as [l'|nl].
      + destruct (lt_irrefl k l').
      + apply (path_sigma_prop fn_isProp_lt); exact refl.
    - destruct (dec (x < k)%nat) as [l'|nl].
      + apply (path_sigma_prop fn_isProp_lt); exact refl.
      + destruct (nl (leq_pred' l)).
  Defined.

  Definition fp_fs (u : FinNat (S k)) : fp (fs u) = u.
  Proof.
    destruct u as [x l]; unfold fs; cbn.
    destruct (dec (x < k)%nat) as [l'|nl]; cbn.
    - apply (path_sigma_prop fn_isProp_lt); exact refl.
    - apply (path_sigma_prop fn_isProp_lt). cbn.
      exact (leq_antisym (Overture.fst geq_iff_not_lt nl) (leq_pred' l)).
  Defined.

  Definition fsEqv : FinNat (S k) ≃ FinNat (S k) := mkEqv fs fp fp_fs fs_fp.

  Definition finsuccEqv : Fin (S k) ≃ Fin (S k)
    := Eqv_comp (Eqv_of_Equiv (equiv_fin_finnat (S k)))
         (Eqv_comp fsEqv (Eqv_inv (Eqv_of_Equiv (equiv_fin_finnat (S k))))).

  Definition Fin_isSet (n : ℕ) : isSet (Fin n) := fun x y => fst (Fin_isDecSet n x y).

  (** Definition [def:RmtoS1]: [R_m(base) :≡ Fin m], [R_m(loop) := etop(zs)],
      and the [m]-th power bundle [pow_m :≡ fst : Tot(R_m) → S1]. *)
  Context `{Univalence}.

  Definition Rm : S1 -> Type := S1_rec Type (Fin (S k)) (etop finsuccEqv).

  Definition Rm_isSet (z : S1) : isSet (Rm z)
    := ptrunc_rec (isSet_isProp _)
         (fun p : base = z => trp (fun x => isSet (Rm x)) p (Fin_isSet (S k)))
         (S1_base_paths z).

  Definition TotRmStar : Ustar := (Tot Rm; (base; fin_zero)).

  Definition powm : TotRmStar →* S1star := (@fst S1 Rm; refl).

  Definition powm_covering : isPtdCovering powm
    := fun z => is_ntype_Eqv 0 (fst_fiber_eqv Rm z) (Rm_isSet z).

End FinCycle.

(** Exercise [xca:preim-eq]. *)
Definition comp_l_isEquiv {X : Type} {a b c : X} (r : b = c)
  : isEquiv (fun p : a = b => r ⋅ p).
Proof. destruct r. exact (id_isEquiv _). Defined.

Definition preim_eq {A B C : Type} (f : A -> C) (g : B -> C) (e : A ≃ B)
  (h : forall x, f x = g (fst e x)) (c : C)
  : isEquiv (fun w : fiber f c => ((fst e (fst w); h (fst w) ⋅ snd w) : fiber g c)).
Proof.
  refine (comp_isEquiv (f := tot (fun a (p : c = f a) => h a ⋅ p))
            (g := fun w : {a : A & c = g (fst e a)} => ((fst e (fst w); snd w) : fiber g c))
            (tot_isEquiv _ (fun a => comp_l_isEquiv (h a))) _).
  exact (isEquiv_of_IsEquiv _
           (H := equiv_isequiv (equiv_functor_sigma_pb (Q := fun b => c = g b)
                                  (Equiv_of_Eqv e)))).
Defined.

(** Definition [def:subgroup-zet-of-cycle]: [H_t :≡ {n : ℤ | t^n = id}],
    and the first part of [lem:cycle-order-point-ap]. *)
Section Orders.

  Context `{Univalence} {X : Type} (sX : isSet X) (t : X ≃ X).

  Definition Ht (n : ℤ) : PropU
    := ((tpow t n = idmap); Pi_isSet (fun _ => sX) _ _).

  Definition Ht_point (cy : isCycle t) (x : X) (n : ℤ)
    : (fst (Ht n) -> tpow t n x = x) × (tpow t n x = x -> fst (Ht n)).
  Proof.
    refine (fun e => ptw e x; _).
    intro e. apply ptw_inv. intro x'.
    refine (ptrunc_rec (sX _ _) _ (snd cy x x')). intros [j ej].
    refine (ap (tpow t n) ej @ (tpow_add sX t j n x)^ @ ap (fun w => tpow t w x) (zadd_comm j n)
            @ tpow_add sX t n j x @ ap (tpow t j) e @ ej^).
  Defined.

  (** Loops at [(base, x)] in [∑_{z:S1} E(z)] correspond to
      [∑_{n:ℤ} (t^n(x) = x)], via the winding number of the projection. *)
  Definition trp_E_loopexp (y : Int) (x : X)
    : trp (E t) (loopexp loop y) x = tpow t (fromInt y) x.
  Proof.
    induction y as [|n IH|n IH] using Int_ind.
    - exact refl.
    - refine (ap (fun r : base = base => trp (E t) r x) (loopexp_succ_r loop _) @ _).
      refine (transport_pp (E t) _ _ _ @ trp_E_loop t _ @ ap (fst t) IH @ _).
      exact ((tpow_zs sX t _ x)^ @ ap (fun w => tpow t w x) (fromInt_succ _)^).
    - refine (ap (fun r : base = base => trp (E t) r x) (loopexp_pred_r loop _) @ _).
      refine (transport_pp (E t) _ _ _ @ trp_E_loopV t _ @ ap (eqinv (snd t)) IH @ _).
      exact ((tpow_zp sX t _ x)^ @ ap (fun w => tpow t w x) (fromInt_pred _)^).
  Defined.

  Definition trp_E_loopZ (n : ℤ) (x : X) : trp (E t) (loopZ n) x = tpow t n x
    := trp_E_loopexp (toInt n) x @ ap (fun w => tpow t w x) (fromInt_toInt n).

  Definition trp_ap_fst {Z : Type} {P : Z -> Type} {u v : {z : Z & P z}} (p : u = v)
    : trp P (ap fst p) (snd u) = snd v
    := match p with refl => refl end.

  Definition loopsAE (x : X)
    : (((base; x) : AE t) = (base; x)) -> {n : ℤ & tpow t n x = x}
    := fun p => (fst wdg (ap fst p);
                 (trp_E_loopZ _ x)^ @ ap (fun q : base = base => trp (E t) q x) (loopZ_wdg (ap fst p))
                 @ trp_ap_fst p).

  Definition loopsAE_inv (x : X) (w : {n : ℤ & tpow t n x = x})
    : ((base; x) : AE t) = (base; x)
    := pathpair (Y := E t) (loopZ (fst w)) (trp_E_loopZ (fst w) x @ snd w).


  Definition split' {u v : AE t} (p : u = v)
    : {q : fst u = fst v & trp (E t) q (snd u) = snd v}
    := (ap fst p; trp_ap_fst p).

  Definition split'_isEquiv (u v : AE t) : isEquiv (@split' u v).
  Proof.
    assert (h : forall p : u = v, pathsplit p = split' p) by (intro p; destruct p; exact refl).
    refine (trp isEquiv (ptw_inv h) _).
    exact (iso_to_isEquiv pathsplit (fun pq => pathpair (fst pq) (snd pq))
             pathpair_pathsplit (fun pq => pathsplit_pathpair (fst pq) (snd pq))).
  Defined.

  Definition loopsAE_reindex (x : X)
    : {q : base = base & trp (E t) q x = x} -> {n : ℤ & tpow t n x = x}
    := fun w => (fst wdg (fst w);
                 (trp_E_loopZ _ x)^ @ ap (fun q : base = base => trp (E t) q x)
                                         (loopZ_wdg (fst w)) @ snd w).

  Definition loopsAE_reindex_isEquiv (x : X) : isEquiv (loopsAE_reindex x).
  Proof.
    refine (iso_to_isEquiv _ (fun w => (loopZ (fst w); trp_E_loopZ (fst w) x @ snd w)) _ _).
    - intro w. apply (path_sigma_prop (fun q => sX _ _)). exact (loopZ_wdg _).
    - intro w. apply (path_sigma_prop (fun n => sX _ _)). exact (wdg_loopZ _).
  Defined.

  (** The equivalence of [lem:cycle-order-point-ap]: [((base,x) = (base,x)) ≃
      ∑_{n:ℤ} (t^n(x) = x)], whose first component is the winding number of
      the projected loop. *)
  Definition loopsAE_isEquiv (x : X) : isEquiv (loopsAE x)
    := comp_isEquiv (split'_isEquiv ((base; x) : AE t) (base; x)) (loopsAE_reindex_isEquiv x).

  (** The image of [(a = a) → (base = base) ≃ ℤ] (with [a :≡ (base, x)]) is
      [H_t], for a cycle [(X,t)]. *)
  Definition image_loops_Ht (cy : isCycle t) (x : X) (n : ℤ)
    : (ptrunc {p : ((base; x) : AE t) = (base; x) & fst wdg (ap fst p) = n}
       -> fst (Ht n))
      × (fst (Ht n) -> ptrunc {p : ((base; x) : AE t) = (base; x) & fst wdg (ap fst p) = n}).
  Proof.
    refine (ptrunc_rec (snd (Ht n)) _; _).
    - intros [p e]. apply (snd (Ht_point cy x n)).
      exact (ap (fun w => tpow t w x) e^ @ snd (loopsAE x p)).
    - intro h. refine (trunc (loopsAE_inv x (n; fst (Ht_point cy x n) h); _)).
      exact (ap (fst wdg) (ap_fst_pathpair _ _) @ wdg_loopZ n).
  Defined.

End Orders.
