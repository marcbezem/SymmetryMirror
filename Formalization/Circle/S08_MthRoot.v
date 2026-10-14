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

    - Powers of the root: [(ᵐ√t)^{mq}(i,x) = (i, t^q(x))] for [q : ℤ]
      ([root_pow]).
    - Lemma [lem:m-root-id] and its converse: [(ᵐ√t)^n = id] iff [n = mq]
      with [t^q = id] ([m_root_id], [m_root_id_conv], [Ht_root]); to avoid
      Euclidean division of negative integers, negative [n] are reduced to
      positive ones.
    - The [m]-th root of a cycle is a cycle ([root_isCycle], [rho_cyc]).
    - Identifications of cycles from identifications in [Endo]
      ([cyc_path]); cycles with the same [H] are merely identified, and
      pointed ones uniquely ([cyc_merely_eq], [cyc_pointed_path]).
    - Lemma [lem:sum-cycle-point-contr], for the component of any cycle
      ([sum_cycle_point_contr]).
    - Lemma [lem:deg-m-on-Cyc]: [ρ_m : Cyc_0 →* Cyc_0] and
      [ρ_m : Cyc_n →* Cyc_{mn}] ([rho_Cyc0], [rho_Cyc0_pt], [rho_Cycm],
      [rho_Cycm_pt]).  Instead of the book's explicit equivalence
      [φ(k, r) :≡ k + mr], the identifications come from [lem:IdCycle]:
      [H_{(ℤ,zs)} = {0}], [H_{(Fin n, zs)} = nℤ] (the standard [n]-cycle is
      the [n]-th root of the trivial cycle), and [H_{ᵐ√t} = mH_t].
    - [X/m] ([Xm]) and lemma [lem:X-mod-m-chosen] ([X_mod_m_chosen]).

    Left out (not yet formalized)
    - The identification of [ρ_m] with the degree [m] map, [ρ_m c = c dg_m],
      and exercise [xca:pointed-maps-circle].
    - Construction [thm:fiber-cdg] (the fiber of [ρ_m] at [(X,t)] is
      [P × X/m]).
 *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core Spaces.Nat.Core Spaces.Int
  Spaces.Circle Spaces.Finite.Fin Spaces.Finite.FinNat Spaces.Nat.Division.
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

(** Powers of the [m]-th root, for a permutation [t] of a set [X]. *)
Section RootPowers.

  Context `{Univalence} (k : ℕ) {X : Type} (sX : isSet X) (t : X ≃ X).

  Definition sFX : isSet (FN k × X) := Sigma_isSet (FinNat_isSet k) (fun _ => sX).

  Definition Rt : (FN k × X) ≃ (FN k × X) := rootEqv k t.

  Definition pow_comm (a b : ℤ) (y : X) : tpow t a (tpow t b y) = tpow t b (tpow t a y)
    := (tpow_add sX t b a y)^ @ ap (fun w => tpow t w y) (zadd_comm b a) @ tpow_add sX t a b y.

  Definition tpow_neg' (n : ℤ) (y : X) : tpow t n (tpow t (zneg n) y) = y
    := pow_comm n (zneg n) y @ tpow_neg sX t n y.

  (** [(ᵐ√t)^{mj}(i, x) = (i, t^j(x))] for [j : ℕ]. *)
  Definition root_pow_nat (i : ℕ) (li : (i < S k)%nat) (j : ℕ)
    : forall x : X, nat_iter (S k * j)%nat (root k (fst t)) (((i; li) : FN k); x)
                    = ((i; li) : FN k; tpow t (iplus j) x).
  Proof.
    induction j as [|j IH]; intro x.
    - exact (ap (fun n => nat_iter n (root k (fst t)) (((i; li) : FN k); x))
               (nat_mul_zero_r (S k))).
    - refine (ap (fun n => nat_iter n (root k (fst t)) (((i; li) : FN k); x))
                (nat_mul_succ_r (S k) j) @ _).
      refine (nat_iter_add (S k * j)%nat (S k) (root k (fst t)) _ @ _).
      refine (ap (fun w => nat_iter (S k * j)%nat (root k (fst t)) w) (root_m k (fst t) i li x) @ _).
      exact (IH (fst t x) @ ap (fun y => ((i; li) : FN k; y)) (pow_comm (iplus j) (iplus 1) x)).
  Defined.

  Definition zmul_neg (a b : ℤ) : zmul a (zneg b) = zneg (zmul a b)
    := toInt_inj (y := zneg (zmul a b))
         (toInt_zmul _ _ @ ap (int_mul (toInt a)) (toInt_zneg b)
          @ int_mul_neg_r _ _ @ ap int_neg (toInt_zmul a b)^ @ (toInt_zneg _)^).

  (** [(ᵐ√t)^{mq}(i, x) = (i, t^q(x))] for [q : ℤ]. *)
  Definition root_pow (q : ℤ) (w : FN k × X)
    : tpow Rt (zmul (iplus (S k)) q) w = (fst w; tpow t q (snd w)).
  Proof.
    destruct w as [[i li] x]. revert q x.
    refine (ℤ_ind_prop _ (fun q => Pi_isProp (fun x => sFX _ _)) _ _).
    - intros j x. refine (ap (fun n => tpow Rt n _) (iplus_mul (S k) j)^ @ _).
      exact (root_pow_nat i li j x).
    - intros [j] x.
      pose (z := (((i; li) : FN k); tpow t (zneg (iplus j)) x) : FN k × X).
      assert (e : tpow Rt (zmul (iplus (S k)) (iplus j)) z = (((i; li) : FN k); x)).
      { refine (ap (fun n => tpow Rt n z) (iplus_mul (S k) j)^ @ _).
        exact (root_pow_nat i li j _ @ ap (fun y => ((i; li) : FN k; y)) (tpow_neg' _ x)). }
      refine (ap (fun n => tpow Rt n _) (zmul_neg (iplus (S k)) (iplus j)) @ _).
      exact (ap (tpow Rt (zneg (zmul (iplus (S k)) (iplus j)))) e^ @ tpow_neg sFX Rt _ z).
  Defined.

  (** Lemma [lem:m-root-id]: if [(ᵐ√t)^n = id] (and [X] is nonempty), then
      [n = mq] with [t^q = id]; and conversely. *)
  Definition root_id_nat (a : ℕ) (x0 : X) (h : tpow Rt (iplus a) = idmap)
    : {q : ℕ & (a = S k * q)%nat × (tpow t (iplus q) = idmap)}.
  Proof.
    pose (q := (a / S k)%nat). pose (r := (a mod S k)%nat).
    pose (lr := nat_mod_lt_r a (S k) _ : (r < S k)%nat).
    assert (ea : (a = S k * q + r)%nat) by exact (nat_div_mod_spec a (S k)).
    assert (E : forall x, tpow Rt (iplus a) (fn0 k; x) = (((r; lr) : FN k); tpow t (iplus q) x)).
    { intro x. refine (ap (fun n => nat_iter n (root k (fst t)) (fn0 k; x)) ea @ _).
      refine (nat_iter_add _ _ _ _ @ _).
      refine (ap (fun w => nat_iter (S k * q)%nat (root k (fst t)) w)
                (root_up k (fst t) r 0%nat (leq_succ (leq_zero_l k)) lr x) @ _).
      exact (root_pow_nat r lr q x). }
    assert (r0 : r = 0%nat).
    { exact (ap (fun w : FN k × X => fst (fst w)) ((E x0)^ @ ptw h _)). }
    refine (q; (ea @ ap (fun s => (S k * q + s)%nat) r0 @ nat_add_zero_r _; _)).
    apply ptw_inv. intro x.
    exact (ap (fun w : FN k × X => snd w) ((E x)^ @ ptw h _)).
  Defined.

  Definition m_root_id (n : ℤ) (x0 : X) (h : tpow Rt n = idmap)
    : Ex (fun q : ℤ => (n = zmul (iplus (S k)) q) × (tpow t q = idmap)).
  Proof.
    revert n h.
    refine (ℤ_ind_prop (fun n => tpow Rt n = idmap -> _) (fun n => fun_isProp ptrunc_isProp) _ _).
    - intros a h. destruct (root_id_nat a x0 h) as [q [ea hq]].
      exact (trunc (iplus q; (ap iplus ea @ iplus_mul (S k) q; hq))).
    - intros [a] h.
      assert (h' : tpow Rt (iplus a) = idmap).
      { apply ptw_inv. intro w.
        exact (ap (tpow Rt (iplus a)) (ptw h w)^ @ tpow_neg sFX Rt (iminus (negN a)) w). }
      destruct (root_id_nat a x0 h') as [q [ea hq]].
      refine (trunc (zneg (iplus q); (_ ; _))).
      + exact (ap zneg (ap iplus ea @ iplus_mul (S k) q) @ (zmul_neg _ _)^).
      + apply ptw_inv. intro y.
        exact (ap (tpow t (zneg (iplus q))) (ptw hq y)^ @ tpow_neg sX t _ y).
  Defined.

  Definition m_root_id_conv (q : ℤ) (hq : tpow t q = idmap)
    : tpow Rt (zmul (iplus (S k)) q) = idmap
    := ptw_inv (fun w => root_pow q w @ ap (fun y => (fst w; y)) (ptw hq (snd w))).

  (** The [m]-th root of a cycle is a cycle. *)
  Definition up_conn (a a' : ℕ) (la : (a < S k)%nat) (la' : (a' < S k)%nat) (y : X)
    (le : (a <= a')%nat)
    : fst (conn_by Rt ((((a; la) : FN k); y)) ((((a'; la') : FN k); y))).
  Proof.
    pose (e := nat_add_sub_r_cancel le : (a + (a' - a) = a')%nat).
    pose (l := trp (fun n => (n < S k)%nat) e^ la').
    refine (trunc (iplus (a' - a); _)).
    refine (_ @ (root_up k (fst t) (a' - a) a la l y)^).
    exact (pair_path k (FN_path k e^) refl).
  Defined.

  Definition root_isCycle (cy : isCycle t) : isCycle Rt.
  Proof.
    refine (ptrunc_rec ptrunc_isProp (fun x0 => trunc ((fn0 k; x0) : FN k × X)) (fst cy); _).
    intros [[a la] x] [[a' la'] x'].
    refine (conn_by_trans sFX Rt _ ((((a; la) : FN k); x')) _ _ _).
    - refine (ptrunc_rec ptrunc_isProp _ (snd cy x x')). intros [n e].
      refine (trunc (zmul (iplus (S k)) n; _)).
      exact (ap (fun y => (((a; la) : FN k); y)) e @ (root_pow n ((((a; la) : FN k); x)))^).
    - destruct (leq_dichotomy a a') as [le|gt].
      + exact (up_conn a a' la la' x' le).
      + exact (conn_by_sym sFX Rt _ _ (up_conn a' a la' la x' (leq_succ_l gt))).
  Defined.

  (** The subset [H] of the [m]-th root: [n ∈ H_{ᵐ√t}] iff [n = mq] with
      [q ∈ H_t] ([lem:m-root-id] and its converse). *)
  Definition Ht_root (cy : isCycle t) (n : ℤ)
    : (fst (Ht sFX Rt n) -> Ex (fun q => (n = zmul (iplus (S k)) q) × fst (Ht sX t q)))
      × (Ex (fun q => (n = zmul (iplus (S k)) q) × fst (Ht sX t q)) -> fst (Ht sFX Rt n)).
  Proof.
    refine (fun h => ptrunc_rec ptrunc_isProp (fun x0 => m_root_id n x0 h) (fst cy); _).
    refine (ptrunc_rec (snd (Ht sFX Rt n)) _). intros [q [e hq]].
    exact (trp (fun w => fst (Ht sFX Rt w)) e^ (m_root_id_conv q hq)).
  Defined.

End RootPowers.

(** Identifications of cycles come from identifications in [Endo]. *)
Section CycPaths.

  Context `{Univalence}.

  Definition cyc_endo (c : Cyc) : Endo := (fst (fst c); fst (fst (snd c))).

  Definition CycP (w : Endo) : Type
    := isSet (fst w) × {tE : isEquiv (snd w) & isCycle ((snd w; tE) : fst w ≃ fst w)}.

  Definition CycP_isProp (w : Endo) : isProp (CycP w)
    := prod_isProp (isSet_isProp _)
         (Sigma_isProp (isEquiv_isProp _)
            (fun tE => prod_isProp ptrunc_isProp
                         (Pi_isProp (fun _ => Pi_isProp (fun _ => ptrunc_isProp))))).

  Definition cyc_of (v : {w : Endo & CycP w}) : Cyc
    := ((fst (fst v); fst (snd v)); ((snd (fst v); fst (snd (snd v))); snd (snd (snd v)))).

  Definition cyc_path (c d : Cyc) (e : cyc_endo c = cyc_endo d) : c = d
    := ap cyc_of (path_sigma_prop CycP_isProp
         (u := (cyc_endo c; (snd (fst c); (snd (fst (snd c)); snd (snd c)))))
         (v := (cyc_endo d; (snd (fst d); (snd (fst (snd d)); snd (snd d))))) e).

  Definition ap_carrier_cyc_of {u v : {w : Endo & CycP w}} (P : u = v)
    : ap (fun c : Cyc => fst (fst c)) (ap cyc_of P) = ap (fun w : Endo => fst w) (ap fst P)
    := match P with refl => refl end.

  Definition ap_carrier_cyc_path (c d : Cyc) (e : cyc_endo c = cyc_endo d)
    : ap (fun c : Cyc => fst (fst c)) (cyc_path c d e) = ap (fun w : Endo => fst w) e
    := ap_carrier_cyc_of (path_sigma_prop CycP_isProp
         (u := (cyc_endo c; (snd (fst c); (snd (fst (snd c)); snd (snd c)))))
         (v := (cyc_endo d; (snd (fst d); (snd (fst (snd d)); snd (snd d))))) e)
       @ ap (ap (fun w : Endo => fst w)) (ap_fst_pathpair _ _).

  (** Cycles with the same subset [H] are merely identified
      ([lem:IdCycle]), and pointed cycles even uniquely. *)
  Definition Hiffc (c d : Cyc) : Type
    := Hiff (snd (fst c)) (snd (fst d)) (fst (snd c)) (fst (snd d)).

  Definition cyc_merely_eq (c d : Cyc) (hH : Hiffc c d) : ptrunc (c = d)
    := ptrunc_rec ptrunc_isProp (fun e => trunc (cyc_path c d e))
         (IdCycle_31 (fst (snd c)) (fst (snd d)) (snd (snd c)) (snd (snd d))
            (IdCycle_23 (snd (fst c)) (snd (fst d)) (fst (snd c)) (fst (snd d))
                        (snd (snd c)) (snd (snd d)) hH)).

  Definition cyc_pointed_path (c d : Cyc) (hH : Hiffc c d)
    (x0 : fst (fst c)) (y0 : fst (fst d)) : c = d
    := cyc_path c d (eqinv (snd (endo_paths_eqv _ _))
         (fst (fst (IdCycle_23 (snd (fst c)) (snd (fst d)) (fst (snd c)) (fst (snd d))
                                (snd (snd c)) (snd (snd d)) hH x0 y0)))).

  (** Lemma [lem:sum-cycle-point-contr]: for any cycle [c], the type of
      pointed cycles in the component of [c] is contractible. *)
  Definition sum_cycle_point_contr (c : Cyc)
    : isContr {w : component Cyc c & fst (fst (fst w))}.
  Proof.
    refine (ptrunc_rec (isContr_isProp _) _ (fst (snd (snd c)))). intro x0.
    refine (((c; trunc refl); x0); _).
    intros [[d m] y].
    pose (hH := IdCycle_12 (snd (fst c)) (snd (fst d)) (fst (snd c)) (fst (snd d))
                  (ptrunc_rec ptrunc_isProp (fun p => trunc (ap cyc_endo p)) m) : Hiffc c d).
    pose (z := fst (IdCycle_23 (snd (fst c)) (snd (fst d)) (fst (snd c)) (fst (snd d))
                      (snd (snd c)) (snd (snd d)) hH x0 y)).
    pose (E := eqinv (snd (endo_paths_eqv _ _)) (fst z)).
    pose (P := path_sigma_prop (fun _ => ptrunc_isProp)
                 (u := (c; trunc refl) : component Cyc c) (v := (d; m)) (cyc_path c d E)).
    refine (pathpair P _).
    refine (transport_compose idmap (fun w : component Cyc c => fst (fst (fst w))) P x0 @ _).
    refine (ap (fun r => transport idmap r x0)
              (ap_compose fst (fun c : Cyc => fst (fst c)) P
               @ ap (ap (fun c : Cyc => fst (fst c))) (ap_fst_pathpair _ _)
               @ ap_carrier_cyc_path c d E) @ _).
    refine ((endo_fun_trp E x0)^ @ _).
    exact (ap (fun w : {e : _ & _} => fst (fst w) x0) (eqinv_r (snd (endo_paths_eqv _ _)) (fst z))
           @ snd z).
  Defined.

End CycPaths.

(** Lemma [lem:deg-m-on-Cyc]: [ρ_m] maps [Cyc_0] to [Cyc_0] and [Cyc_n] to
    [Cyc_{mn}], as pointed maps.  Instead of the explicit equivalence
    [φ(k, r) :≡ k + mr], we compare the subsets [H] ([lem:IdCycle]):
    [H_{ᵐ√t} = m H_t] by [lem:m-root-id]. *)
Section DegMOnCyc.

  Context `{Univalence} (k : ℕ).

  Definition rho_cyc (c : Cyc) : Cyc
    := ((FN k × fst (fst c); sFX k (snd (fst c)));
        (Rt k (fst (snd c)); root_isCycle k (snd (fst c)) (fst (snd c)) (snd (snd c)))).

  Definition Hc_rho (c : Cyc) (n : ℤ)
    : (fst (Hc (rho_cyc c) n) -> Ex (fun q => (n = zmul (iplus (S k)) q) × fst (Hc c q)))
      × (Ex (fun q => (n = zmul (iplus (S k)) q) × fst (Hc c q)) -> fst (Hc (rho_cyc c) n))
    := Ht_root k (snd (fst c)) (fst (snd c)) (snd (snd c)) n.

  Definition zadd_0_l (n : ℤ) : zadd (iplus 0) n = n
    := toInt_inj (y := n) (toInt_zadd (iplus 0) n).

  (** [H] of the infinite cycle [(ℤ, zs)] is [{0}]. *)
  Definition Hc_Z (n : ℤ) : (fst (Hc Zcyc n) -> n = iplus 0) × (n = iplus 0 -> fst (Hc Zcyc n))
    := (fun h => (zadd_0_l n)^ @ ptw h (iplus 0);
        fun e : n = iplus 0 => trp (fun w => fst (Hc Zcyc w)) e^
                                  (refl : fst (Hc Zcyc (iplus 0)))).

  Definition Hiff_rho_Z : Hiffc (rho_cyc Zcyc) Zcyc.
  Proof.
    intro n. refine (fun h => _; fun h => _).
    - refine (snd (Hc_Z n) _).
      refine (ptrunc_rec (ℤ_isSet _ _) _ (fst (Hc_rho Zcyc n) h)). intros [q [e hq]].
      exact (e @ ap (zmul (iplus (S k))) (fst (Hc_Z q) hq)).
    - apply (snd (Hc_rho Zcyc n)). apply trunc.
      exact (iplus 0; (fst (Hc_Z n) h; snd (Hc_Z _) refl)).
  Defined.

  Definition rho_Z_path : rho_cyc Zcyc = Zcyc
    := cyc_pointed_path (rho_cyc Zcyc) Zcyc Hiff_rho_Z (fn0 k; iplus 0) (iplus 0).

  Definition rho_Cyc0 (w : Cyc0) : Cyc0
    := (rho_cyc (fst w);
        ptrunc_rec ptrunc_isProp (fun p => trunc (ap rho_cyc p ⋅ rho_Z_path⁻¹)) (snd w)).

  Definition rho_Cyc0_pt : rho_Cyc0 (Zcyc; trunc refl) = (Zcyc; trunc refl)
    := path_sigma_prop (fun _ => ptrunc_isProp) (u := rho_Cyc0 (Zcyc; trunc refl))
         (v := (Zcyc; trunc refl)) rho_Z_path.

  (** The trivial cycle [(𝟙, id)], whose [H] is all of [ℤ]. *)
  Definition tpow_id {X : Type} (sX : isSet X) (n : ℤ) (x : X) : tpow (idEqv X) n x = x.
  Proof.
    revert n. refine (ℤ_ind_prop _ (fun n => sX _ _) _ _).
    - intro j. induction j as [|j IH]; [exact refl | exact IH].
    - intros [j]. induction j as [|j IH]; [exact refl|].
      exact (eqinv_l (snd (idEqv X)) _ @ IH).
  Defined.

  Definition True_isSet : isSet True := prop_is_set True_isProp.

  Definition unit_isCycle : isCycle (idEqv True)
    := (trunc tt; fun x x' => trunc (iplus 0; True_isProp _ _)).

  Definition unitcyc : Cyc := ((True; True_isSet); (idEqv True; unit_isCycle)).

  (** The standard [m]-cycle on [∑_i (i < m)] is the [m]-th root of the
      trivial cycle, so its [H] is [mℤ]. *)
  Definition fn_root_eqv : FinNat (S k) ≃ (FN k × True)
    := mkEqv (fun i => ((i; tt) : FN k × True)) fst (fun i => refl)
             (fun w => match w with (i; tt) => refl end).

  Definition fn_root_comm (i : FinNat (S k))
    : fst fn_root_eqv (fs k i) = root k idmap (fst fn_root_eqv i).
  Proof.
    destruct i as [i l]. unfold fs, root. cbn.
    destruct (dec (i < k)%nat); exact refl.
  Defined.

  Definition Hc_FinNat (n : ℤ)
    : (fst (Ht (FinNat_isSet k) (fsEqv k) n) -> Ex (fun q => n = zmul (iplus (S k)) q))
      × (Ex (fun q => n = zmul (iplus (S k)) q) -> fst (Ht (FinNat_isSet k) (fsEqv k) n)).
  Proof.
    pose (e := fn_root_eqv).
    pose (to := Ht_transfer (FinNat_isSet k) (sFX k True_isSet) (fsEqv k) (Rt k (idEqv True)) e
                  fn_root_comm n).
    pose (back := Ht_transfer (sFX k True_isSet) (FinNat_isSet k) (Rt k (idEqv True)) (fsEqv k)
                    (Eqv_inv e) (inv_comm (fsEqv k) (Rt k (idEqv True)) e fn_root_comm) n).
    refine (fun h => _; fun h => back _).
    - refine (ptrunc_rec ptrunc_isProp _ (fst (Hc_rho unitcyc n) (to h))).
      intros [q [eq _]]. exact (trunc (q; eq)).
    - apply (snd (Hc_rho unitcyc n)).
      refine (ptrunc_rec ptrunc_isProp _ h). intros [q eq].
      exact (trunc (q; (eq; ptw_inv (tpow_id True_isSet q)))).
  Defined.

End DegMOnCyc.

Section HcFinSec.

  Context `{Univalence} (j : ℕ).

  (** [H] of the standard [n]-cycle [(Fin n, zs)] is [nℤ]. *)
  Definition Hc_Fin (n : ℤ)
    : (fst (Hc (Fincyc j) n) -> Ex (fun q => n = zmul (iplus (S j)) q))
      × (Ex (fun q => n = zmul (iplus (S j)) q) -> fst (Hc (Fincyc j) n)).
  Proof.
    pose (e := Eqv_of_Equiv (equiv_fin_finnat (S j))).
    assert (he : forall x, fst e (fst (finsuccEqv j) x) = fst (fsEqv j) (fst e x))
      by (intro x; exact (eqinv_r (snd e) _)).
    pose (to := Ht_transfer (Fin_isSet (S j)) (FinNat_isSet j) (finsuccEqv j) (fsEqv j) e he n).
    pose (back := Ht_transfer (FinNat_isSet j) (Fin_isSet (S j)) (fsEqv j) (finsuccEqv j)
                    (Eqv_inv e) (inv_comm (finsuccEqv j) (fsEqv j) e he) n).
    exact (fun h => fst (Hc_FinNat j n) (to h); fun h => back (snd (Hc_FinNat j n) h)).
  Defined.

End HcFinSec.

Section DegMOnCycN.

  Context `{Univalence} (k j : ℕ).

  Definition zmul_assoc_nat (a b : ℕ) (p : ℤ)
    : zmul (iplus a) (zmul (iplus b) p) = zmul (iplus (a * b)%nat) p.
  Proof.
    apply toInt_inj.
    refine (toInt_zmul (iplus a) (zmul (iplus b) p)
            @ ap (int_mul (int_of_nat a)) (toInt_zmul (iplus b) p) @ _).
    refine (int_mul_assoc _ _ _ @ _ @ (toInt_zmul (iplus (a * b)%nat) p)^).
    exact (ap (fun z => int_mul z (toInt p)) (int_nat_mul a b)).
  Defined.

  (** For [m = k+1] and [n = j+1], [mn = (j + k(j+1)) + 1] by definition. *)
  Definition jmn : ℕ := (j + k * S j)%nat.

  Definition Hiff_rho_Fin : Hiffc (rho_cyc k (Fincyc j)) (Fincyc jmn).
  Proof.
    intro n. refine (fun h => _; fun h => _).
    - change (fst (Hc (Fincyc jmn) n)).
      refine (snd (Hc_Fin jmn n) _).
      refine (ptrunc_rec ptrunc_isProp _ (fst (Hc_rho k (Fincyc j) n) h)). intros [q [e hq]].
      refine (ptrunc_rec ptrunc_isProp _ (fst (Hc_Fin j q) hq)). intros [p ep].
      exact (trunc (p; e @ ap (zmul (iplus (S k))) ep @ zmul_assoc_nat (S k) (S j) p)).
    - change (fst (Hc (rho_cyc k (Fincyc j)) n)).
      refine (snd (Hc_rho k (Fincyc j) n) _).
      refine (ptrunc_rec ptrunc_isProp _ (fst (Hc_Fin jmn n) h)). intros [p ep].
      refine (trunc (zmul (iplus (S j)) p; (ep @ (zmul_assoc_nat (S k) (S j) p)^; _))).
      exact (snd (Hc_Fin j _) (trunc (p; refl))).
  Defined.

  Definition rho_Fin_path : rho_cyc k (Fincyc j) = Fincyc jmn
    := cyc_pointed_path _ _ Hiff_rho_Fin (fn0 k; fin_zero) fin_zero.

  Definition rho_Cycm (w : Cycm j) : Cycm jmn
    := (rho_cyc k (fst w);
        ptrunc_rec ptrunc_isProp (fun p => trunc (ap (rho_cyc k) p ⋅ rho_Fin_path⁻¹)) (snd w)).

  Definition rho_Cycm_pt : rho_Cycm (Fincyc j; trunc refl) = (Fincyc jmn; trunc refl)
    := path_sigma_prop (fun _ => ptrunc_isProp) (u := rho_Cycm (Fincyc j; trunc refl))
         (v := (Fincyc jmn; trunc refl)) rho_Fin_path.

End DegMOnCycN.

(** Integer arithmetic used below, via [toInt]. *)
Definition zmul_add (a b c : ℤ) : zmul a (zadd b c) = zadd (zmul a b) (zmul a c).
Proof.
  apply toInt_inj.
  refine (toInt_zmul _ _ @ ap (int_mul (toInt a)) (toInt_zadd b c) @ int_dist_l _ _ _ @ _).
  exact (ap011 int_add (toInt_zmul a b)^ (toInt_zmul a c)^ @ (toInt_zadd _ _)^).
Defined.

Definition neg_normal (k a : ℕ)
  : zadd (iplus (k * a)%nat) (zmul (iplus (S k)) (zneg (iplus a))) = iminus (negN a).
Proof.
  apply (toInt_inj (y := iminus (negN a))).
  rewrite toInt_zadd, toInt_zmul, toInt_zneg.
  change (int_add (int_of_nat (k * a)%nat)
            (int_mul (int_of_nat (S k)) (int_neg (int_of_nat a))) = int_neg (int_of_nat a)).
  rewrite int_mul_neg_r, (int_nat_mul (S k) a).
  change (int_add (int_of_nat (k * a)%nat) (int_neg (int_of_nat (a + k * a)%nat))
          = int_neg (int_of_nat a)).
  rewrite <- (int_nat_add a (k * a)%nat), int_neg_add.
  rewrite int_add_assoc, (int_add_comm (int_of_nat (k * a)%nat) (int_neg (int_of_nat a))).
  rewrite <- int_add_assoc, int_add_neg_r, int_add_0_r. exact refl.
Defined.

Definition int_of_nat_inj {a b : ℕ} (e : int_of_nat a = int_of_nat b) : a = b
  := iplus_inj (toInt_inj (x := iplus a) (y := iplus b) e).

Definition int_sub_eq (x y z : Int) (e : int_add x (int_neg y) = z) : x = int_add z y.
Proof. destruct e. rewrite <- int_add_assoc, int_add_neg_l, int_add_0_r. exact refl. Defined.

(** If [i, j < m] and [i - j = mu], then [i = j]. *)
Section SmallDiff.

  Context `{Funext} (k : ℕ).

  Definition small_diff_pos (i j v : ℕ) (li : (i < S k)%nat)
    (e : zadd (iplus i) (zneg (iplus j)) = zmul (iplus (S k)) (iplus (S v))) : Empty.
  Proof.
    pose (e' := ap toInt e).
    rewrite toInt_zadd, toInt_zmul, toInt_zneg in e'.
    pose (e2 := int_sub_eq _ _ _ e'). cbn in e2.
    rewrite (int_nat_mul (S k) (S v)), (int_nat_add (S k * S v)%nat j) in e2.
    pose (e3 := int_of_nat_inj e2 : i = (S k * S v + j)%nat).
    assert (le : (S k <= i)%nat).
    { rewrite e3, nat_mul_succ_r.
      exact (leq_trans (leq_add_l (S k) (S k * v)%nat) (leq_add_r _ j)). }
    exact (lt_irrefl _ (leq_trans li le)).
  Defined.

  Definition small_diff (i j : ℕ) (li : (i < S k)%nat) (lj : (j < S k)%nat) (u : ℤ)
    (e : zadd (iplus i) (zneg (iplus j)) = zmul (iplus (S k)) u) : i = j.
  Proof.
    revert u e.
    refine (ℤ_ind_prop (fun u => zadd (iplus i) (zneg (iplus j)) = zmul (iplus (S k)) u -> i = j)
              (fun u => fun_isProp (ℕ_isSet _ _)) _ _).
    - intros [|v] e.
      + pose (e' := ap toInt e). rewrite toInt_zadd, toInt_zneg in e'.
        exact (int_of_nat_inj (int_sub_eq _ _ _ e')).
      + destruct (small_diff_pos i j v li e).
    - intros [[|v]] e.
      + pose (e' := ap toInt e). rewrite toInt_zadd, toInt_zneg in e'.
        exact (int_of_nat_inj (int_sub_eq _ _ _ e')).
      + refine (match small_diff_pos j i v lj _ with end).
        refine ((zsub_neg (iplus i) (iplus j))^ @ ap zneg e @ _).
        refine ((zmul_neg _ _)^ @ _). exact refl.
  Defined.

End SmallDiff.

(** The set [X/m :≡ X/∼_m], with [x ∼_m x'] iff [x' = t^{mr}(x)] for some
    [r : ℤ], and lemma [lem:X-mod-m-chosen]. *)
Section XmodM.

  Context `{Univalence} (k : ℕ) {X : Type} (sX : isSet X) (t : X ≃ X) (cy : isCycle t).

  Definition simm (x x' : X) : PropU
    := (ptrunc {r : ℤ & x' = tpow t (zmul (iplus (S k)) r) x}; ptrunc_isProp).

  Definition simm_refl (x : X) : fst (simm x x) := trunc (iplus 0; refl).

  Definition simm_sym (x x' : X) (h : fst (simm x x')) : fst (simm x' x).
  Proof.
    refine (ptrunc_rec ptrunc_isProp _ h). intros [r e].
    refine (trunc (zneg r; _)).
    refine ((tpow_neg sX t _ x)^ @ _).
    exact (ap (tpow t (zneg (zmul (iplus (S k)) r))) e^
           @ ap (fun w => tpow t w x') (zmul_neg _ _)^).
  Defined.

  Definition simm_trans (x x' x'' : X) (h : fst (simm x x')) (h' : fst (simm x' x''))
    : fst (simm x x'').
  Proof.
    refine (ptrunc_rec ptrunc_isProp _ h). intros [r e].
    refine (ptrunc_rec ptrunc_isProp _ h'). intros [r' e'].
    refine (trunc (zadd r r'; _)).
    refine (e' @ ap (tpow t _) e @ (tpow_add sX t _ _ x)^ @ _).
    exact (ap (fun w => tpow t w x) (zmul_add _ _ _)^).
  Defined.

  Definition Xm : Type := quot simm.

  Definition clsm (x : X) : Xm := cls simm x.

  Definition clsm_iff (x x' : X)
    : (clsm x = clsm x' -> fst (simm x x')) × (fst (simm x x') -> clsm x = clsm x')
    := cls_eq_iff simm simm_refl simm_sym simm_trans x x'.

  (** [P]: [m] divides the order of [t], i.e. [H_t ⊆ mℤ]. *)
  Definition Pdiv : Type
    := forall n, fst (Ht sX t n) -> Ex (fun q => n = zmul (iplus (S k)) q).

  Definition fXm (x0 : X) (i : FN k) : Xm := clsm (tpow t (iplus (fst i)) x0).

  Definition fXm_surj (x0 : X) : isSurj (fXm x0).
  Proof.
    refine (im_ind simm _ (fun _ => ptrunc_isProp) _). intro x.
    refine (ptrunc_rec ptrunc_isProp _ (snd cy x0 x)). intros [n en].
    (* a nonnegative exponent [a] with [t^a(x₀) ∼_m t^n(x₀)] *)
    assert (A : Ex (fun a : ℕ => fst (simm (tpow t (iplus a) x0) (tpow t n x0)))).
    { revert n en. refine (ℤ_ind_prop (fun n => _ -> _) (fun n => fun_isProp ptrunc_isProp) _ _).
      - intros a _. exact (trunc (a; simm_refl _)).
      - intros [a] _. refine (trunc ((k * a)%nat; trunc (zneg (iplus a); _))).
        refine (ap (fun w => tpow t w x0) (neg_normal k a)^ @ _).
        exact (tpow_add sX t _ _ x0). }
    refine (ptrunc_rec ptrunc_isProp _ A). intros [a ha].
    pose (q := (a / S k)%nat). pose (r := (a mod S k)%nat).
    pose (lr := nat_mod_lt_r a (S k) _ : (r < S k)%nat).
    refine (trunc (((r; lr) : FN k); _)).
    apply (snd (clsm_iff _ _)).
    refine (simm_trans x (tpow t (iplus a) x0) _ _ _).
    - exact (simm_sym _ _ (simm_trans _ _ _ ha (trunc (iplus 0; en)))).
    - refine (simm_sym _ _ (trunc (iplus q; _))).
      refine (ap (fun b => nat_iter b (fst t) x0) (nat_div_mod_spec a (S k)) @ _).
      refine (nat_iter_add _ _ _ _ @ _).
      exact (ap (fun w => tpow t w _) (iplus_mul (S k) q)).
  Defined.

  Definition fXm_inj (hP : Pdiv) (x0 : X) : isInj (fXm x0).
  Proof.
    apply (cancel_isInj (quot_isSet simm)). intros [i li] [j lj] e.
    apply (path_sigma_prop (fn_isProp_lt k)). cbn.
    refine (ptrunc_rec (ℕ_isSet _ _) _ (fst (clsm_iff _ _) e)). intros [r er].
    pose (d := zadd (zadd (iplus i) (zmul (iplus (S k)) r)) (zneg (iplus j))).
    assert (ed : tpow t d x0 = x0).
    { refine (tpow_add sX t _ _ x0 @ _).
      refine (ap (tpow t (zneg (iplus j))) (tpow_add sX t _ _ x0 @ er^) @ _).
      exact (tpow_neg sX t _ x0). }
    refine (ptrunc_rec (ℕ_isSet _ _) _ (hP d (snd (Ht_point sX t cy x0 d) ed))). intros [s es].
    refine (small_diff k i j li lj (zadd s (zneg r)) _).
    refine (_ @ ap (zadd _) (zmul_neg _ _)^ @ (zmul_add _ _ _)^).
    refine (_ @ ap (fun w => zadd w (zneg (zmul (iplus (S k)) r))) es).
    apply toInt_inj. unfold d.
    repeat first [rewrite toInt_zadd | rewrite toInt_zneg].
    rewrite <- (int_add_assoc (toInt (iplus i)) (toInt (zmul (iplus (S k)) r))).
    rewrite (int_add_comm (toInt (zmul (iplus (S k)) r)) (int_neg (toInt (iplus j)))).
    rewrite int_add_assoc, <- (int_add_assoc _ (toInt (zmul (iplus (S k)) r))).
    rewrite int_add_neg_r, int_add_0_r. exact refl.
  Defined.

  Definition X_mod_m_chosen (hP : Pdiv) (x0 : X) : isEquiv (fXm x0)
    := inj_surj_isEquiv (fXm_inj hP x0) (fXm_surj x0).

End XmodM.
