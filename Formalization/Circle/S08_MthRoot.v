(** * Section 3.8 The m-th root: coverings over the components of Cyc

    Part of Chapter 3 ([circle.tex]); see [Circle.v] for an overview of
    the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - [def:Cyc-components]: [Cyc0] and [Cycm k] (for [m = k+1]), the
      components of [Cyc] at [(ℤ, zs)] and [(Fin m, zs)].
    - Construction [con:root]: the [m]-th root [ᵐ√t] on [𝟙m × X], with
      [𝟙m] represented as [∑_{i:ℕ} (i < m)] ([FinNat]).
    - Lemma [lem:root-pres-equiv], with an explicit inverse
      ([root_isEquiv]).
    - [(ᵐ√t)^m (i, x) = (i, t(x))] ([root_m]).
    - Definition [def:root]: the formal [m]-th root [ρ_m] on [∑_X (X → X)]
      ([rho]).

    Left out (not yet formalized)
    - That [ρ_m] preserves cycles, [lem:deg-m-on-Cyc], the identification
      of [ρ_m] with the degree [m] map ([dg_m]) and
      [xca:pointed-maps-circle], [lem:sum-cycle-point-contr],
      [lem:m-root-id], [lem:X-mod-m-chosen] and [thm:fiber-cdg]. *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core Spaces.Nat.Core Spaces.Int
  Spaces.Circle Spaces.Finite.Fin Spaces.Finite.FinNat.
From SymmetryMirror Require Export Circle.S07_Permutations.

Local Open Scope uf_scope.

(** ** 3.8 The [m]-th root: coverings over the components of [Cyc] *)

(** Definition [def:Cyc-components]: [Cyc_0] (infinite cycles) and the
    components [Cyc_m] of the standard [m]-cycles ([m = k+1]). *)
Definition Cyc0 `{Univalence} : Type := component Cyc Zcyc.

Definition Cycm `{Univalence} (k : ℕ) : Type := component Cyc (Fincyc k).

(** Construction [con:root]: the [m]-th root of [t : X → X] on
    [𝟙m × X], with [𝟙m] represented as [∑_{i:ℕ} (i < m)] ([FinNat]):
    [(i, x) ↦ (i+1, x)] for [i < m-1] and [(m-1, x) ↦ (0, t(x))]. *)
Section Root.

  Context (k : ℕ) {X : Type}.

  Definition FN : Type := FinNat (S k).

  Definition root (t : X -> X) (w : FN × X) : FN × X
    := match dec (fst (fst w) < k)%nat with
       | inl l => ((S (fst (fst w)); leq_succ l); snd w)
       | inr _ => (fn0 k; t (snd w))
       end.

  Definition root_inv (t' : X -> X) (w : FN × X) : FN × X
    := match fst w with
       | (O; _) => ((k; leq_refl (S k)); t' (snd w))
       | (S i; l) => ((i; leq_succ_l l); snd w)
       end.

  Definition FN_path {i j : ℕ} {l : (i < S k)%nat} {l' : (j < S k)%nat} (e : i = j)
    : ((i; l) : FN) = (j; l')
    := path_sigma_prop (fn_isProp_lt k) (u := (i; l)) (v := (j; l')) e.

  Definition pair_path {u v : FN} {x y : X} (e : u = v) (e' : x = y)
    : ((u; x) : FN × X) = (v; y)
    := ap011 (fun a b => (a; b) : FN × X) e e'.

  (** Lemma [lem:root-pres-equiv], with an explicit inverse. *)
  Definition root_isEquiv (t : X ≃ X) : isEquiv (root (fst t)).
  Proof.
    refine (iso_to_isEquiv _ (root_inv (eqinv (snd t))) _ _).
    - intros [[i l] x]. unfold root. cbn.
      destruct (dec (i < k)%nat) as [l'|nl]; cbn.
      + exact (pair_path (FN_path refl) refl).
      + exact (pair_path (FN_path (leq_antisym (Overture.fst geq_iff_not_lt nl) (leq_pred' l)))
                         (eqinv_l (snd t) x)).
    - intros [[i l] x]. destruct i as [|i]; unfold root_inv, root; cbn.
      + destruct (dec (k < k)%nat) as [l'|_]; [destruct (lt_irrefl k l')|].
        exact (pair_path (FN_path refl) (eqinv_r (snd t) x)).
      + destruct (dec (i < k)%nat) as [l'|nl]; [| destruct (nl (leq_pred' l))].
        exact (pair_path (FN_path refl) refl).
  Defined.

  Definition rootEqv (t : X ≃ X) : (FN × X) ≃ (FN × X)
    := (root (fst t); root_isEquiv t).


  (** Iterating the [m]-th root [m] times gives [(i, x) ↦ (i, t(x))], hence
      the name. *)
  Definition root_up (t : X -> X) (j : ℕ)
    : forall (i : ℕ) (li : (i < S k)%nat) (l : (i + j < S k)%nat) (x : X),
      nat_iter j (root t) (((i; li) : FN); x) = (((i + j)%nat; l) : FN; x).
  Proof.
    induction j as [|j IH]; intros i li l x.
    - exact (pair_path (FN_path (nat_add_zero_r i)^) refl).
    - assert (e : (i + S j = S (i + j))%nat) by exact (nat_add_succ_r i j).
      assert (l' : (i + j < S k)%nat)
        by exact (leq_succ_l (trp (fun n => (S n <= S k)%nat) e l)).
      refine (ap (root t) (IH i li l' x) @ _). unfold root. cbn.
      destruct (dec (i + j < k)%nat) as [l''|nl].
      + exact (pair_path (FN_path e^) refl).
      + destruct (nl (trp (fun n => (n <= k)%nat) e (leq_pred' l))).
  Defined.

  Definition root_last (t : X -> X) (x : X)
    : root t (((k; leq_refl (S k)) : FN); x) = (fn0 k; t x).
  Proof.
    unfold root. cbn.
    destruct (dec (k < k)%nat) as [l'|nl]; [destruct (lt_irrefl k l') | exact refl].
  Defined.

  Definition root_m (t : X -> X) (i : ℕ) (li : (i < S k)%nat) (x : X)
    : nat_iter (S k) (root t) (((i; li) : FN); x) = ((i; li) : FN; t x).
  Proof.
    pose (le_ik := leq_pred' li).
    assert (e : (i + S (k - i) = S k)%nat)
      by exact (nat_add_succ_r i (k - i) @ ap S (nat_add_sub_r_cancel le_ik)).
    refine (ap (fun n => nat_iter n (root t) (((i; li) : FN); x)) e^ @ _).
    refine (nat_iter_add i (S (k - i)) (root t) _ @ _).
    assert (lk : (i + (k - i) < S k)%nat)
      by exact (trp (fun n => (n < S k)%nat) (nat_add_sub_r_cancel le_ik)^ (leq_refl (S k))).
    refine (ap (fun w => nat_iter i (root t) (root t w)) (root_up t (k - i) i li lk x) @ _).
    refine (ap (fun w => nat_iter i (root t) (root t (w; x)))
              (FN_path (l' := leq_refl (S k)) (nat_add_sub_r_cancel le_ik)) @ _).
    refine (ap (fun w => nat_iter i (root t) w) (root_last t x) @ _).
    exact (root_up t i 0%nat (leq_succ (leq_zero_l k)) li (t x)).
  Defined.

End Root.

(** Definition [def:root]: the formal [m]-th root function on [Endo]. *)
Definition rho (k : ℕ) (w : Endo) : Endo := (FN k × fst w; root k (snd w)).
