(** * Formalization of Sections 2.23 - 2.24 of [intro-uf.tex]

    ** Summary of this formalization

    Sections 2.23 - 2.24 are formalized in this file, which builds on
    [IntroUF.v] - [IntroUF6.v] and [Bridge.v].  It compiles, with nothing
    admitted.  [Print Assumptions]: the pigeonhole principle uses no
    axioms; [Funext] and [Univalence] are used only where needed.

    Book notions defined from Coq-HoTT notions: [pred :≡ nat_pred], and
    [Fin] is the library's [Fin] (same name; [Fin(succ(n)) ≡ Succ(Fin(n))]
    by definition).  Own definitions: [le], [lt] (the book's
    [m ≤ n :≡ ∑_k (k + m = n)], equivalent to the library's inductive
    [<=], [<], whose lemmas we reuse), [Pmin], [μ_P] ([mu]), [Succ]
    ([SuccT]), [isFinSet], [FinSet], [FinSet_n], [Card], [lookup].

    2.23 More on natural numbers
    - [≤] and [<] are propositions; exercise [xca:try-your-luck-N]
      (injectivity of [succ], commutativity, associativity and
      distributivity, transitivity, monotonicity, [≤] iff [<] or [=],
      antisymmetry, asymmetry of [<]).
    - [lem:dec-eq+order-N], and [ℕ] is a set by Hedberg's theorem.
    - [def:Nwellordered]: bounded search [μ_P] as in the book, its
      correctness, and [min(P)] for decidable [P] that merely has a
      witness.
    - [lem:PHP], with explicit witnesses; the proof searches first for a
      collision with [f(N+1)] and only otherwise uses the book's [g].
    - [cor:Fin-n-injective], derived from [Fin(m) = Fin(n) → m = n]
      (library [nat_eq_fin_equiv]) instead of from PHP.
    - [lem:euclid-div] as contractibility of the type of quotients and
      remainders, using the library's division instead of bounded search.

    2.24 The type of finite sets
    - Exercise [xca:finite-types]: the elements of [Fin 0], [Fin 1],
      [Fin 2]; [Fin 1 ≃ True], [Fin 2 ≃ Bool]; [Fin(n) ≃ ∑_k (k < n)] (via
      the library's [equiv_fin_finnat]); [Fin m = Fin n → m = n].
    - [isFinSet], [lem:maxonefinitetype], [FinSet], [FinSet_n], [Card];
      [FinSet ≃ ∑_n FinSet_n]; [FinSet_0] and [FinSet_1] are contractible.
    - Exercise [xca:finsets-decidable].
    - Exercise [xca:2-element-sets], first two parts: [T = T] is a
      2-element set, and [¬ ∏_{T : FinSet_2} (T = 𝟚)] (by univalence).
    - Exercise [xca:tabulation] ([lookup]) and [cor:lists-truncated].
    - Remark [rem:subset-of-fin-set]: a proposition is a finite set iff
      it is decidable.
    - Exercise [xca:dec-quant-finset].
    - Exercise [xca:fin-sum-of-finsets] and exercise
      [xca:dec-quot-finite-set], via a bridge between [isFinSet] and the
      library's class [Finite] ([finite_sigma], [fcard_prod], [finadd],
      [finite_quotient]).

    Left out
    - Exercise [xca:2-element-sets], last two parts
      ([∏_T ((T = T) = 𝟚)] and [∏_T (T = (𝟚 = T))]).
    - The remark that [FinSet] is essentially small is formalized in
      [IntroUF8.v] ([FinSet_essSmall]).

    ** Conventions

    Continuation of [IntroUF.v] - [IntroUF6.v] and [Bridge.v], with the
    same conventions: path composition [q ⋅ p :≡ p ∙ q], fibers with
    [y = f x], and notions that occur definitionally in Coq-HoTT defined
    from the library notion and used under the book's name.  Results that
    need univalence assume Coq-HoTT's [Univalence].

    The library's order [leq] on [nat] is an inductive family, whereas
    the book defines [m ≤ n :≡ ∑_k (k + m = n)]; we use the book's
    definitions [le], [lt] and prove them equivalent to the library's
    [<=] and [<] (written with [%nat]), whose lemmas we then reuse. *)

From HoTT Require Import Basics Types.Sigma Types.Equiv Types.Universe
  Types.Forall Types.Bool Truncations.Core Colimits.Quotient Spaces.Nat.Core
  Spaces.Nat.Division Spaces.Finite.Fin Spaces.Finite.FinNat
  Spaces.Finite.Finite Spaces.List.Core.
From SymmetryMirror Require Import IntroUF IntroUF2 IntroUF3 Bridge IntroUF4
  IntroUF5 IntroUF6.

Local Open Scope uf_scope.

(** ** 2.23 More on natural numbers *)

Definition ℕ_isSet : isSet ℕ := IsHSet_isSet ishset_nat.

(** The predecessor [pred(0) :≡ 0], [pred(succ(n)) :≡ n] is the library's
    [nat_pred]. *)
Definition pred : ℕ -> ℕ := nat_pred.

Definition pred_0 : pred 0%nat = 0%nat := refl.
Definition pred_succ (n : ℕ) : pred (succ n) = n := refl.

(** Definition [def:orderonN]. *)
Definition le (m n : ℕ) : Type := {k : ℕ & add k m = n}.
Definition lt (m n : ℕ) : Type := {k : ℕ & (add k m = n) × (k ≠ 0%nat)}.

(** Comparison with the library's order. *)
Definition le_leq {m n : ℕ} (h : le m n) : (m <= n)%nat
  := trp (fun t => (m <= t)%nat) (snd h) (leq_add_r m (fst h)).

Definition leq_le {m n : ℕ} (h : (m <= n)%nat) : le m n
  := let w := equiv_leq_add m n h in (fst w; nat_add_comm m (fst w) @ snd w).

Definition lt_ltlib {m n : ℕ} (h : lt m n) : (m < n)%nat.
Proof.
  destruct h as [k [e nz]]. destruct k as [|k].
  - destruct (nz refl).
  - apply (trp (fun t => (m < t)%nat) e).
    exact (trp (fun t => (S m <= t)%nat) (nat_add_succ_r m k)^
             (leq_succ (leq_add_r m k))).
Defined.

Definition ltlib_lt {m n : ℕ} (h : (m < n)%nat) : lt m n.
Proof.
  destruct (equiv_leq_add (S m) n h) as [k e].
  refine (S k; (_; fun z => zero_ne_succ k z⁻¹)).
  exact (nat_add_succ_r m k @ ap S (nat_add_comm m k) @ (nat_add_succ_r k m)^ @ e).
Defined.

(** Both [m ≤ n] and [m < n] are propositions. *)
Definition le_isProp (m n : ℕ) : isProp (le m n).
Proof.
  intros [k e] [k' e'].
  apply (path_sigma_prop (fun _ => ℕ_isSet _ _)).
  exact (isinj_nat_add_l m k k' (e @ e'^)).
Defined.

Definition lt_isProp `{Funext} (m n : ℕ) : isProp (lt m n).
Proof.
  intros [k [e nz]] [k' [e' nz']].
  apply (path_sigma_prop (fun k => prod_isProp (ℕ_isSet _ _) (neg_isProp _))).
  exact (isinj_nat_add_l m k k' (e @ e'^)).
Defined.

(** Exercise [xca:try-your-luck-N]. *)
Section TryYourLuck.

  Definition succ_inj {n m : ℕ}
    : ((succ n = succ m) -> n = m) × (n = m -> succ n = succ m)
    := (path_nat_succ n m; ap succ).

  Definition add_comm (n m : ℕ) : add n m = add m n := nat_add_comm m n.

  Definition add_assoc (n m k : ℕ) : add n (add m k) = add (add n m) k
    := (nat_add_assoc k m n)^.

  Definition mul_comm (n m : ℕ) : mul n m = mul m n := nat_mul_comm n m.

  Definition mul_assoc (n m k : ℕ) : mul n (mul m k) = mul (mul n m) k
    := nat_mul_assoc n m k.

  Definition mul_add_distr (m n k : ℕ)
    : mul m (add n k) = add (mul m n) (mul m k)
    := nat_dist_l m k n.

  Definition le_trans {m n k : ℕ} (h : le m n) (h' : le n k) : le m k
    := leq_le (leq_trans (le_leq h) (le_leq h')).

  Definition lt_trans' {m n k : ℕ} (h : lt m n) (h' : lt n k) : lt m k
    := ltlib_lt (lt_trans (lt_ltlib h) (lt_ltlib h')).

  Definition le_add {m n : ℕ} (p : ℕ) (h : le m n) : le (add m p) (add n p)
    := leq_le (nat_add_l_monotone p (le_leq h)).

  Definition lt_add {m n : ℕ} (p : ℕ) (h : lt m n) : lt (add m p) (add n p)
    := ltlib_lt (nat_add_l_strictly_monotone p (lt_ltlib h)).

  Definition le_mul {m n : ℕ} (p : ℕ) (h : le m n) : le (mul m p) (mul n p)
    := leq_le (nat_mul_r_monotone p (le_leq h)).

  Definition le_refl (n : ℕ) : le n n := (0%nat; nat_add_zero_r n).

  Definition le_iff_lt_or_eq (m n : ℕ)
    : (le m n -> lt m n ⨿ (m = n)) × (lt m n ⨿ (m = n) -> le m n).
  Proof.
    split.
    - intros [k e]. destruct k as [|k].
      + exact (inr ((nat_add_zero_r m)^ @ e)).
      + exact (inl (S k; (e; fun z => zero_ne_succ k z⁻¹))).
    - intros [[k [e _]]|e].
      + exact (k; e).
      + exact (0%nat; nat_add_zero_r m @ e).
  Defined.

  Definition le_antisym (m n : ℕ)
    : (le m n × le n m -> m = n) × (m = n -> le m n × le n m)
    := (fun h => leq_antisym (le_leq (fst h)) (le_leq (snd h));
        fun e => match e with refl => (le_refl m; le_refl m) end).

  Definition lt_asym (m n : ℕ) : ¬ (lt m n × lt n m)
    := fun h => lt_irrefl m (lt_trans (lt_ltlib (fst h)) (lt_ltlib (snd h))).

End TryYourLuck.

(** Lemma [lem:dec-eq+order-N]. *)
Definition eq_dec (n m : ℕ) : isDecidable (n = m) := dec_paths n m.

Definition le_dec (m n : ℕ) : isDecidable (le m n)
  := match dec (m <= n)%nat with
     | inl h => inl (leq_le h)
     | inr nh => inr (fun l => nh (le_leq l))
     end.

Definition lt_dec (m n : ℕ) : isDecidable (lt m n)
  := match dec (m < n)%nat with
     | inl h => inl (ltlib_lt h)
     | inr nh => inr (fun l => nh (lt_ltlib l))
     end.

(** By Hedberg's theorem, [ℕ] is a (decidable) set. *)
Definition ℕ_isDecSet : isDecSet ℕ := hedberg eq_dec.

(** Construction [def:Nwellordered]: the least number principle for
    decidable, non-empty subsets of [ℕ], by bounded search [μ_P]. *)
Section LeastNumber.

  Context (P : ℕ -> PropU) (d : forall n, isDecidable (fst (P n))).

  Definition Pmin (n : ℕ) : Type
    := fst (P n) × (forall m, fst (P m) -> le n m).

  (** Bounded search: [μ_P(0) :≡ 0]; [μ_P(succ(n)) :≡ μ_P(n)] if
      [μ_P(n) < n], and otherwise [n] if [P(n)] and [succ(n)] if not. *)
  Fixpoint mu (n : ℕ) : ℕ
    := match n with
       | O => O
       | S n' => match dec (mu n' < n')%nat with
                 | inl _ => mu n'
                 | inr _ => match d n' with
                            | inl _ => n'
                            | inr _ => S n'
                            end
                 end
       end.

  Definition mu_spec1 (n : ℕ)
    : (mu n <= n)%nat × ((mu n < n)%nat -> fst (P (mu n))).
  Proof.
    induction n as [|n IH].
    - exact (leq_refl 0; fun l => match lt_irrefl 0 l with end).
    - cbn. destruct (dec (mu n < n)%nat) as [l|nl].
      + exact (leq_trans (fst IH) (leq_succ_r (leq_refl n)); fun _ => snd IH l).
      + destruct (d n) as [p|np].
        * exact (leq_succ_r (leq_refl n); fun _ => p).
        * exact (leq_refl (S n); fun l => match lt_irrefl _ l with end).
  Defined.

  Definition mu_spec2 (n m : ℕ) (pm : fst (P m)) : (mu n <= m)%nat.
  Proof.
    induction n as [|n IH].
    - exact (leq_zero_l m).
    - cbn. destruct (dec (mu n < n)%nat) as [l|nl].
      + exact IH.
      + assert (e : mu n = n)
          by exact (leq_antisym (fst (mu_spec1 n)) (Overture.fst leq_iff_not_gt nl)).
        assert (le_nm : (n <= m)%nat) by exact (trp (fun t => (t <= m)%nat) e IH).
        destruct (d n) as [p|np].
        * exact le_nm.
        * assert (ne : n <> m) by (intro q; destruct q; exact (np pm)).
          destruct (Overture.fst neq_iff_lt_or_gt ne) as [lt_nm|gt_nm].
          -- exact lt_nm.
          -- destruct (lt_irrefl _ (lt_leq_lt_trans le_nm gt_nm)).
  Defined.

  Definition mu_Pmin (n : ℕ) (p : fst (P n)) : Pmin (mu (S n))
    := (snd (mu_spec1 (S n)) (leq_succ (mu_spec2 (S n) n p));
        fun m pm => leq_le (mu_spec2 (S n) m pm)).

  Definition Pmin_isProp `{Funext} : isProp {n : ℕ & Pmin n}.
  Proof.
    intros [n [p h]] [n' [p' h']].
    apply (path_sigma_prop (fun n => prod_isProp (snd (P n))
             (Pi_isProp (fun m => fun_isProp (le_isProp n m))))).
    exact (leq_antisym (le_leq (h n' p')) (le_leq (h' n p))).
  Defined.

  Definition min `{Funext} : ptrunc {n : ℕ & fst (P n)} -> {n : ℕ & Pmin n}
    := ptrunc_rec Pmin_isProp (fun w => (mu (S (fst w)); mu_Pmin (fst w) (snd w))).

End LeastNumber.

(** Remark [rem:computations-can-decide]: decisions are used in
    computations, e.g. [dec (mu n < n)] above. *)

(** Bounded search for a decidable property. *)
Definition lt_succ_cases {k b : ℕ} (l : (k < S b)%nat) : (k < b)%nat ⨿ (k = b).
Proof.
  pose (l' := leq_pred' l : (k <= b)%nat).
  destruct (dec_paths k b) as [e|ne].
  - exact (inr e).
  - destruct (Overture.fst neq_iff_lt_or_gt ne) as [lt_kb|gt_kb].
    + exact (inl lt_kb).
    + destruct (lt_irrefl _ (lt_leq_lt_trans l' gt_kb)).
Defined.

Definition bounded_dec (Q : ℕ -> Type) (dq : forall k, isDecidable (Q k))
  : forall b : ℕ, {k : ℕ & (k < b)%nat × Q k} ⨿ (forall k, (k < b)%nat -> ¬ Q k).
Proof.
  intro b. induction b as [|b IH].
  - right. intros k l. destruct (not_lt_zero_r k l).
  - destruct IH as [[k [l q]]|nq].
    + left. exact (k; (lt_trans l (leq_refl (S b)); q)).
    + destruct (dq b) as [q|nq'].
      * left. exact (b; (leq_refl (S b); q)).
      * right. intros k l.
        destruct (lt_succ_cases l) as [l'|e].
        -- exact (nq k l').
        -- destruct e. exact nq'.
Defined.

(** Lemma [lem:PHP], the pigeonhole principle.  We produce the witnesses
    explicitly.  The proof differs slightly from the book's: we first
    search for an [n < N+1] with [f(n) = f(N+1)], and only otherwise
    apply the induction hypothesis to the book's [g]. *)
Definition PHP_lib (N : ℕ) (f : ℕ -> ℕ)
  (hf : forall n, (n < S N)%nat -> (f n < N)%nat)
  : {m : ℕ & {n : ℕ & (m < n)%nat × ((n < S N)%nat × (f n = f m))}}.
Proof.
  revert f hf. induction N as [|N IH]; intros f hf.
  - destruct (not_lt_zero_r _ (hf 0%nat (leq_refl 1))).
  - destruct (bounded_dec (fun k => f k = f (S N)) (fun k => dec_paths _ _) (S N))
      as [[k [lk ek]]|nc].
    + exact (k; (S N; (lk; (leq_refl (S (S N)); ek⁻¹)))).
    + pose (g := fun k => match dec_paths (f k) N with
                          | inl _ => f (S N)
                          | inr _ => f k
                          end).
      assert (hfSN : (f (S N) < S N)%nat) by exact (hf (S N) (leq_refl _)).
      assert (hg : forall k, (k < S N)%nat -> (g k < N)%nat).
      { intros k lk. unfold g. destruct (dec_paths (f k) N) as [e|ne].
        - destruct (lt_succ_cases hfSN) as [l|e2].
          + exact l.
          + destruct (nc k lk (e @ e2^)).
        - destruct (lt_succ_cases (hf k (lt_trans lk (leq_refl _)))) as [l|e2].
          + exact l.
          + destruct (ne e2). }
      destruct (IH g hg) as [m [n [lmn [ln e]]]].
      refine (m; (n; (lmn; (lt_trans ln (leq_refl _); _)))).
      unfold g in e.
      destruct (dec_paths (f n) N) as [en|nen], (dec_paths (f m) N) as [em|nem].
      * exact (en @ em^).
      * destruct (nc m (lt_trans lmn ln) e^).
      * destruct (nc n ln e).
      * exact e.
Defined.

Definition PHP (N : ℕ) (f : ℕ -> ℕ)
  (hf : forall n, lt n (succ N) -> lt (f n) N)
  : {m : ℕ & {n : ℕ & lt m n × (lt n (succ N) × (f n = f m))}}.
Proof.
  destruct (PHP_lib N f (fun n l => lt_ltlib (hf n (ltlib_lt l))))
    as [m [n [lmn [ln e]]]].
  exact (m; (n; (ltlib_lt lmn; (ltlib_lt ln; e)))).
Defined.

(** Exercise [xca:finite-types], part 3: [Fin(n) ≃ ∑_k (k < n)], via the
    library's [equiv_fin_finnat]. *)
Definition Fin_lt_eqv `{Funext} (n : ℕ) : Fin n ≃ {k : ℕ & lt k n}
  := Eqv_comp (Eqv_of_Equiv (equiv_fin_finnat n))
       (tot (fun k (l : (k < n)%nat) => ltlib_lt l);
        tot_isEquiv _ (fun k => snd (Eqv_of_props (IsHProp_isProp (P := (k < n)%nat))
                                       (lt_isProp k n) ltlib_lt lt_ltlib))).

(** Exercise [xca:finite-types], part 4: [Fin m = Fin n] implies [m = n],
    via the library's [nat_eq_fin_equiv]. *)
Definition Fin_paths_eq {m n : ℕ} (e : Fin m = Fin n :> Type) : m = n
  := nat_eq_fin_equiv m n (Equiv_of_Eqv (idtoeqv e)).

(** Corollary [cor:Fin-n-injective].  We derive it from part 4 of
    [xca:finite-types] rather than from the pigeonhole principle. *)
Definition Fin_n_injective `{Funext} {m n : ℕ} (l : lt m n)
  : ({k : ℕ & lt k m} = {k : ℕ & lt k n}) -> False.
Proof.
  intro e.
  pose (E := Eqv_comp (Fin_lt_eqv m) (Eqv_comp (idtoeqv e) (Eqv_inv (Fin_lt_eqv n)))).
  pose (q := nat_eq_fin_equiv m n (Equiv_of_Eqv E)).
  destruct q. exact (lt_irrefl _ (lt_ltlib l)).
Defined.

(** Lemma [lem:euclid-div].  We use the library's division with
    remainder ([nat_div], [nat_mod]) instead of the book's bounded
    search. *)
Definition euclid_div `{Funext} (n m : ℕ) (pos : lt 0%nat m)
  : isContr {q : ℕ & {r : ℕ & lt r m × (n = add (mul q m) r)}}.
Proof.
  pose (pos' := lt_ltlib pos).
  pose (e0 := nat_div_mod_spec n m @ ap (fun t => (t + n mod m)%nat) (nat_mul_comm m _)
              @ nat_add_comm _ _ : n = add (mul (n / m) m) (n mod m)).
  refine ((n / m; (n mod m; (ltlib_lt (nat_mod_lt_r n m pos'); e0)))%nat; _).
  - intros [q [r [l e]]].
    pose (e' := ((nat_div_mod_spec n m)^ @ e
                 @ nat_add_comm _ _ @ ap (fun t => (t + r)%nat) (nat_mul_comm q m))
                : (m * (n / m) + n mod m = m * q + r)%nat).
    destruct (nat_div_mod_unique m _ _ _ _ (nat_mod_lt_r n m pos') (lt_ltlib l) e')
      as [eq er].
    destruct eq, er.
    exact (ap (fun w => ((n / m)%nat; ((n mod m)%nat; w)))
              (prod_isProp (lt_isProp _ _) (ℕ_isSet _ _) _ _)).
Defined.

(** ** 2.24 The type of finite sets *)

(** Definition [def:finiteset]: [Succ(X) :≡ X ⨿ True], and
    [Fin(0) :≡ ∅], [Fin(succ(n)) :≡ Succ(Fin(n))]: this is the library's
    [Fin], which has the same name. *)
Definition SuccT (X : Type) : Type := X ⨿ True.

Definition Fin_0 : Fin 0 = False := refl.
Definition Fin_succ (n : ℕ) : Fin (succ n) = SuccT (Fin n) := refl.

(** Exercise [xca:finite-types], parts 1 and 2. *)
Definition fin1_0 : Fin 1 := inr triv.
Definition fin2_0 : Fin 2 := inl (inr triv).
Definition fin2_1 : Fin 2 := inr triv.

Definition Fin0_elems : Fin 0 -> False := idmap.

Definition Fin1_elems (x : Fin 1) : x = fin1_0
  := match x with inl e => match e with end | inr t => match t with triv => refl end end.

Definition Fin2_elems (x : Fin 2) : (x = fin2_0) ⨿ (x = fin2_1)
  := match x with
     | inl y => inl (ap inl (Fin1_elems y))
     | inr t => inr (match t with triv => refl end)
     end.

Definition Fin1_isProp : isProp (Fin 1)
  := fun x y => (Fin1_elems y)⁻¹ ⋅ Fin1_elems x.

Definition Fin1_True : Fin 1 ≃ True
  := Eqv_of_props Fin1_isProp True_isProp (fun _ => triv) (fun _ => fin1_0).

Definition Fin2_Bool : Fin 2 ≃ Bool.
Proof.
  refine (mkEqv (fun x => match x with inl _ => no | inr _ => yes end)
                (fun b => if b then fin2_1 else fin2_0) _ _).
  - intro x. destruct (Fin2_elems x) as [e|e]; destruct e^; exact refl.
  - intros []; exact refl.
Defined.

(** Definition [def:is-finite]. *)
Definition isFinSet (X : Type) : Type := Ex (fun n : ℕ => X = Fin n).

(** Lemma [lem:maxonefinitetype]. *)
Section MaxOneFiniteType.

  Context {X : Type}.

  Definition card_type : Type := {n : ℕ & ptrunc (X = Fin n)}.

  Definition card_type_isProp : isProp card_type.
  Proof.
    intros [n p] [m q].
    apply (path_sigma_prop (fun _ => ptrunc_isProp)).
    refine (ptrunc_rec (ℕ_isSet _ _) _ p). intro e.
    refine (ptrunc_rec (ℕ_isSet _ _) _ q). intro e'.
    exact (Fin_paths_eq (e' ⋅ e⁻¹)).
  Defined.

  Definition card_type_iff
    : (card_type -> isFinSet X) × (isFinSet X -> card_type)
    := (fun w : card_type =>
          ptrunc_rec ptrunc_isProp
            (fun e : X = Fin (fst w) => trunc ((fst w; e) : {n : ℕ & X = Fin n}))
            (snd w);
        ptrunc_rec card_type_isProp
          (fun w : {n : ℕ & X = Fin n} => (fst w; trunc (snd w)) : card_type)).

End MaxOneFiniteType.

(** Definition [def:groupoidFin]. *)
Definition FinSet : Type := {S : SetU & isFinSet (fst S)}.

Definition FinSet_n (n : ℕ) : Type := {S : SetU & ptrunc (Fin n = fst S :> Type)}.

Definition Card (S : FinSet) : ℕ := fst (snd card_type_iff (snd S)).

Definition Card_spec (S : FinSet) : ptrunc (fst (fst S) = Fin (Card S))
  := snd (snd card_type_iff (snd S)).

(** [FinSet ≃ ∑_{n:ℕ} FinSet_n], by [lem:maxonefinitetype]. *)
Definition FinSet_sum_eqv : FinSet ≃ {n : ℕ & FinSet_n n}.
Proof.
  refine (Eqv_comp (tot (fun S => snd card_type_iff);
                    tot_isEquiv _ (fun S => snd (Eqv_of_props ptrunc_isProp
                                                   card_type_isProp _
                                                   (fst card_type_iff)))) _).
  refine (Eqv_comp (sigma_comm SetU ℕ (fun S n => ptrunc (fst S = Fin n))) _).
  pose (F := fun (n : ℕ) (S : SetU) => Eqv_of_props (ptrunc_isProp (T := fst S = Fin n))
                          (ptrunc_isProp (T := Fin n = fst S :> Type))
                          (ptrunc_rec ptrunc_isProp (fun e => trunc e⁻¹))
                          (ptrunc_rec ptrunc_isProp (fun e => trunc e⁻¹))).
  pose (Fn := fun n => (tot (fun S => fst (F n S)); tot_isEquiv _ (fun S => snd (F n S)))
                       : {S : SetU & ptrunc (fst S = Fin n)} ≃ FinSet_n n).
  exact (tot (fun n => fst (Fn n)); tot_isEquiv _ (fun n => snd (Fn n))).
Defined.

(** [FinSet_0] and [FinSet_1] are contractible. *)
Definition FinSet_0_isContr `{Univalence} : isContr (FinSet_n 0).
Proof.
  refine ((exist (fun X : Type => isSet X) (Fin 0) (prop_is_set False_isProp);
           trunc refl); _).
  intros [[S sS] u].
  apply (path_sigma_prop (fun _ => ptrunc_isProp)).
  apply (path_sigma_prop (fun X => isSet_isProp X)). cbn.
  pose (nS := ptrunc_rec (neg_isProp S)
                (fun e : Fin 0 = S :> Type => fun s => ptoe e⁻¹ s) u).
  exact (etop (Eqv_of_props False_isProp (fun a b => match nS a with end)
                 (fun x => match x with end) (fun s => match nS s with end))).
Defined.

Definition FinSet_1_isContr `{Univalence} : isContr (FinSet_n 1).
Proof.
  refine ((exist (fun X : Type => isSet X) (Fin 1) (prop_is_set Fin1_isProp);
           trunc refl); _).
  intros [[S sS] u].
  apply (path_sigma_prop (fun _ => ptrunc_isProp)).
  apply (path_sigma_prop (fun X => isSet_isProp X)). cbn.
  pose (hs := ptrunc_rec (Sigma_isProp (isProp_isProp S) (fun h => h))
                (fun e : Fin 1 = S :> Type =>
                   ((isProp_Eqv (idtoeqv e) Fin1_isProp; ptoe e fin1_0)
                    : {h : isProp S & S})) u).
  exact (etop (Eqv_of_props Fin1_isProp (fst hs) (fun _ => snd hs) (fun _ => fin1_0))).
Defined.

(** Exercise [xca:finsets-decidable]. *)
Definition isDecSet_isProp `{Funext} (X : Type) : isProp (isDecSet X)
  := Pi_isProp (fun x => Pi_isProp (fun y =>
       Sigma_isProp (isProp_isProp (x = y)) (fun h => lem_isProp h))).

Definition Fin_isDecSet (n : ℕ) : isDecSet (Fin n)
  := hedberg (fun x y => dec_paths x y).

Definition finset_isDecSet `{Funext} {X : Type} (h : isFinSet X) : isDecSet X.
Proof.
  refine (ptrunc_rec (isDecSet_isProp X) _ h). intros [n e].
  exact (trp isDecSet e⁻¹ (Fin_isDecSet n)).
Defined.

(** Exercise [xca:2-element-sets], first two parts. *)
Section TwoElementSets.

  Context `{Univalence}.

  (** [Bool = Bool] is equivalent to [Bool] (using [xca:C2]). *)
  Definition BoolPaths_Bool : (Bool = Bool :> Type) ≃ Bool.
  Proof.
    pose (swap_no := ptw (ap fst (ptoe_etop swapEqv)) yes : ptoe swap yes = no).
    pose (back := fun b : Bool => if b then (refl : Bool = Bool :> Type) else swap).
    refine (mkEqv (fun p : Bool = Bool :> Type => ptoe p yes) back _ _).
    - intro p. destruct (Bool_paths_cases p) as [e|e].
      + revert p e. refine (paths_ind_r _ _ _). exact refl.
      + revert p e. refine (paths_ind_r _ _ _). exact (ap back swap_no).
    - intros []; [exact refl | exact swap_no].
  Defined.

  Definition paths_conj_eqv {A B : Type} (e : A = B) : (A = A) ≃ (B = B).
  Proof. destruct e. exact (idEqv _). Defined.

  Definition Fin2_Bool_path : Fin 2 = Bool :> Type := etop Fin2_Bool.

  (** [T = T] is a 2-element set for every 2-element set [T]. *)
  Definition self_paths_two_element (T : FinSet_n 2)
    : isSet (fst (fst T) = fst (fst T))
      × ptrunc (Fin 2 = (fst (fst T) = fst (fst T)) :> Type).
  Proof.
    destruct T as [[X sX] u]. cbn.
    refine (paths_sets_isSet sX; _).
    refine (ptrunc_rec ptrunc_isProp _ u). intro e.
    apply trunc.
    exact (ap (fun Y : Type => Y = Y) e
           ⋅ etop (Eqv_comp Fin2_Bool
                     (Eqv_inv (Eqv_comp (paths_conj_eqv Fin2_Bool_path) BoolPaths_Bool)))).
  Defined.

  (** [¬ ∏_{T : FinSet_2} (T = 𝟚)]: the swap of [Fin 2] gives a loop at
      [Fin 2] in [FinSet_2], along which such a family would have to be
      invariant. *)
  Definition swapFin : Fin 2 -> Fin 2
    := fun x => match x with inl _ => fin2_1 | inr _ => fin2_0 end.

  Definition swapFin_invol (x : Fin 2) : swapFin (swapFin x) = x.
  Proof. destruct (Fin2_elems x) as [e|e]; destruct e^; exact refl. Defined.

  Definition swapFinEqv : Fin 2 ≃ Fin 2
    := mkEqv swapFin swapFin swapFin_invol swapFin_invol.

  Definition swapF : Fin 2 = Fin 2 :> Type := etop swapFinEqv.

  Definition swapF_ne_refl : swapF ≠ refl.
  Proof.
    intro e.
    pose (h := ap fst (ptoe_etop swapFinEqv) : ptoe swapF = swapFin).
    pose (h' := ap ptoe e ⋅ h⁻¹ : swapFin = ptoe (refl (Fin 2 : Type))).
    exact (inl_ne_inr (inr triv) triv (ptw h' fin2_1)).
  Defined.

  Definition Fin2_isSet : isSet (Fin 2) := fun x y => fst (Fin_isDecSet 2 x y).

  Definition Fin2_FinSet2 : FinSet_n 2
    := (exist (fun X : Type => isSet X) (Fin 2) Fin2_isSet; trunc refl).

  Definition cancel_loop {A B : Type} (q : A = A) (x : A = B)
    : trans q⁻¹ x = x -> q = refl.
  Proof.
    destruct x. intro h. exact ((symm_symm q)^ @ ap symm h).
  Defined.

  Definition not_all_two_element_paths
    : ¬ (forall T : FinSet_n 2, fst (fst T) = Fin 2).
  Proof.
    intro s.
    pose (l := path_sigma_prop (u := Fin2_FinSet2) (v := Fin2_FinSet2)
                 (fun _ => ptrunc_isProp)
                 (path_sigma_prop (u := fst Fin2_FinSet2) (v := fst Fin2_FinSet2)
                    (fun X => isSet_isProp X) swapF)).
    pose (a := apD s l).
    assert (t : forall (T T' : FinSet_n 2) (r : T = T') (x : fst (fst T) = Fin 2),
               transport (fun T : FinSet_n 2 => fst (fst T) = Fin 2) r x
               = trans (ap (fun T : FinSet_n 2 => fst (fst T)) r)⁻¹ x).
    { intros T T' r x. destruct r. exact (trans_1p x)⁻¹. }
    assert (ap1 : ap (fun T : FinSet_n 2 => fst (fst T)) l = swapF).
    { refine (ap_compose fst fst l @ _).
      refine (ap (ap fst) (ap_fst_pathpair _ _) @ _).
      exact (ap_fst_pathpair _ _). }
    apply swapF_ne_refl.
    exact (ap1^ @ cancel_loop _ (s Fin2_FinSet2) ((t _ _ l _)^ @ a)).
  Defined.

End TwoElementSets.

(** Exercise [xca:tabulation]: [lookup : X^* ≃ ∑_{n:ℕ} (Fin(n) → X)].  A
    list [x ℓ] is sent to [(succ(n), i ↦ …)] where the new element [x] is
    at index [inr(triv)] and the elements of [ℓ] at the indices [inl(i)]. *)
Section Tabulation.

  Context {X : Type}.

  Definition lookup_step (x : X) (w : {n : ℕ & Fin n -> X})
    : {n : ℕ & Fin n -> X}
    := (S (fst w); fun i => match i with inl i' => snd w i' | inr _ => x end).

  Fixpoint lookup (l : X^*) : {n : ℕ & Fin n -> X}
    := match l with
       | nil => (0%nat; fun i : Fin 0 => match i with end)
       | cons x l' => lookup_step x (lookup l')
       end.

  Fixpoint unlookup_n (n : ℕ) : (Fin n -> X) -> X^*
    := match n with
       | O => fun _ => nil
       | S n' => fun f => cons (f (inr triv)) (unlookup_n n' (fun i => f (inl i)))
       end.

  Definition unlookup (w : {n : ℕ & Fin n -> X}) : X^* := unlookup_n (fst w) (snd w).

  Definition lookup_isEquiv `{Funext} : isEquiv lookup.
  Proof.
    refine (iso_to_isEquiv lookup unlookup _ _).
    - intro l. induction l as [|x l IH].
      + exact refl.
      + exact (ap (cons x) IH).
    - intros [n f]. revert f. induction n as [|n IH]; intro f.
      + exact (ap (fun g => (0%nat; g) : {n : ℕ & Fin n -> X})
                  (ptw_inv (fun i : Fin 0 => match i with end))).
      + refine (ap (lookup_step (f (inr triv))) (IH (fun i => f (inl i))) @ _).
        refine (ap (fun g => (S n; g) : {n : ℕ & Fin n -> X}) (ptw_inv _)).
        intros [i|t]; [exact refl | destruct t; exact refl].
  Defined.

  Definition lookup_eqv `{Funext} : X^* ≃ {n : ℕ & Fin n -> X}
    := (lookup; lookup_isEquiv).

End Tabulation.

(** Corollary [cor:lists-truncated]: for [n ≥ 0], lists of [n]-types are
    [n]-types. *)
Definition prop_ntype (n : ℕ) : forall X : Type, isProp X -> is_ntype n X.
Proof.
  induction n as [|n IH]; intros X h.
  - exact (prop_is_set h).
  - exact (fun x y => IH _ (prop_is_set h x y)).
Defined.

Definition set_ntype (n : ℕ) {X : Type} (s : isSet X) : is_ntype n X
  := match n with
     | O => s
     | S n' => fun x y => prop_ntype n' _ (s x y)
     end.

Definition list_ntype `{Funext} (n : ℕ) {X : Type} (h : is_ntype n X)
  : is_ntype n (X^*)
  := is_ntype_Eqv n (Eqv_inv lookup_eqv)
       (Sigma_ntype n (set_ntype n ℕ_isSet) (fun k => fun_ntype n h)).

(** Remark [rem:subset-of-fin-set]: a proposition is a finite set if and
    only if it is decidable. *)
Definition cardF {X : Type} (h : isFinSet X) : ℕ := fst (snd card_type_iff h).

Definition finprop_dec `{Funext} {p : Type} (hp : isProp p) (f : isFinSet p)
  : isDecidable p.
Proof.
  destruct (snd card_type_iff f) as [n u].
  refine (ptrunc_rec (lem_isProp hp) _ u). intro e.
  destruct n as [|n].
  - exact (inr (fun x => ptoe e x)).
  - exact (inl (ptoe e⁻¹ (inr triv))).
Defined.

Definition dec_finprop `{Univalence} {p : Type} (hp : isProp p)
  (d : isDecidable p) : isFinSet p
  := match d with
     | inl x => trunc (1%nat; etop (Eqv_of_props hp Fin1_isProp
                                     (fun _ => fin1_0) (fun _ => x)))
     | inr nx => trunc (0%nat; etop (Eqv_of_props hp False_isProp nx
                                     (fun e => match e with end)))
     end.

(** Exercise [xca:dec-quant-finset]. *)
Definition Fin_dec_quant `{Funext}
  : forall (n : ℕ) (P : Fin n -> PropU) (d : forall x, isDecidable (fst (P x))),
    isDecidable (Ex (fun x => fst (P x))) × isDecidable (forall x, fst (P x)).
Proof.
  intro n. induction n as [|n IH]; intros P d.
  - exact (inr (ptrunc_rec False_isProp
                  (fun w : {x : Fin 0 & fst (P x)} => match fst w with end));
           inl (fun x : Fin 0 => match x with end)).
  - destruct (IH (fun x => P (inl x)) (fun x => d (inl x))) as [ex al].
    refine (_; _).
    + destruct (d (inr triv)) as [p|np].
      * exact (inl (trunc (inr triv; p))).
      * destruct ex as [u|nu].
        -- exact (inl (ptrunc_rec ptrunc_isProp
                         (fun w : {x : Fin n & fst (P (inl x))} => trunc ((inl (fst w); snd w)
                                          : {x : Fin (S n) & fst (P x)})) u)).
        -- refine (inr (ptrunc_rec False_isProp _)).
           intros [[x|t] q].
           ++ exact (nu (trunc (x; q))).
           ++ destruct t. exact (np q).
    + destruct (d (inr triv)) as [p|np].
      * destruct al as [a|na].
        -- refine (inl _). intros [x|t].
           ++ exact (a x).
           ++ destruct t. exact p.
        -- exact (inr (fun h : forall x, fst (P x) => na (fun x => h (inl x)))).
      * exact (inr (fun h : forall x, fst (P x) => np (h (inr triv)))).
Defined.

Definition dec_quant_path `{Funext} {X : Type} {n : ℕ} (e : X = Fin n :> Type)
  : forall (P : X -> PropU) (d : forall x, isDecidable (fst (P x))),
    isDecidable (Ex (fun x => fst (P x))) × isDecidable (forall x, fst (P x)).
Proof. revert X e. refine (paths_ind_r _ _ _). exact (Fin_dec_quant n). Defined.

Definition finset_dec_quant `{Funext} {X : Type} (h : isFinSet X)
  (P : X -> PropU) (d : forall x, isDecidable (fst (P x)))
  : isDecidable (Ex (fun x => fst (P x))) × isDecidable (forall x, fst (P x))
  := ptrunc_rec (prod_isProp (lem_isProp ptrunc_isProp)
                   (lem_isProp (Pi_isProp (fun x => snd (P x)))))
       (fun w => dec_quant_path (snd w) P d) h.

(** Finite sets in the book's sense versus Coq-HoTT's class [Finite]. *)
Definition isFinSet_Finite `{Univalence} {X : Type} (h : isFinSet X) : Finite X
  := ptrunc_rec (@IsHProp_isProp _ (ishprop_finite X))
       (fun w => Build_Finite X (fst w) (tr (Equiv_of_Eqv (idtoeqv (snd w))))) h.

Definition Finite_isFinSet `{Univalence} {X : Type} (F : Finite X) : isFinSet X
  := ptrunc_rec ptrunc_isProp
       (fun e => trunc ((fcard X; etop (Eqv_of_Equiv e)) : {n : ℕ & X = Fin n}))
       (merely_equiv_fin X).

Definition cardF_fcard `{Univalence} {X : Type} (h : isFinSet X)
  : cardF h = @fcard X (isFinSet_Finite h)
  := ptrunc_ind (fun h => cardF h = @fcard X (isFinSet_Finite h))
       (fun _ => ℕ_isSet _ _) (fun w => refl) h.

Definition isFinSet_Eqv `{Univalence} {A B : Type} (e : A ≃ B)
  (h : isFinSet B) : isFinSet A
  := ptrunc_rec ptrunc_isProp
       (fun w => trunc ((fst w; snd w ⋅ etop e) : {n : ℕ & A = Fin n})) h.

(** Exercise [xca:fin-sum-of-finsets]. *)
Definition sum_finsets_isFinSet `{Univalence} {X : Type} (hX : isFinSet X)
  (F : X -> FinSet) : isFinSet {x : X & fst (fst (F x))}
  := Finite_isFinSet (@finite_sigma X (fun x => fst (fst (F x)))
                        (isFinSet_Finite hX) (fun x => isFinSet_Finite (snd (F x)))).

Definition card_sum_const `{Univalence} {X Y : Type} (hX : isFinSet X)
  (hY : isFinSet Y) (F : X -> Type) (e : forall x, F x ≃ Y)
  (hS : isFinSet {x : X & F x})
  : cardF hS = mul (cardF hX) (cardF hY).
Proof.
  pose (FX := isFinSet_Finite hX). pose (FY := isFinSet_Finite hY).
  pose (FS := isFinSet_Finite hS).
  pose (E := Eqv_comp (tot (fun x => fst (e x)); tot_isEquiv _ (fun x => snd (e x)))
               (binprod_prod X Y)).
  refine (cardF_fcard hS @ _ @ (ap011 nat_mul (cardF_fcard hX) (cardF_fcard hY))^).
  exact (@fcard_equiv' _ _ (Equiv_of_Eqv E) FS (@finite_prod X Y FX FY)
         @ @fcard_prod X Y FX FY).
Defined.

(** The arithmetical sum [∑_{x:X} f(x)] of [f : X → ℕ] over a finite set,
    via the library's [finadd]. *)
Definition finsum `{Univalence} {X : Type} (h : isFinSet X) (f : X -> ℕ) : ℕ
  := @finadd X (isFinSet_Finite h) f.

(** Exercise [xca:dec-quot-finite-set], via the library's [finite_quotient]
    and [xca:quotients-equivalence]. *)
Definition quot_isFinSet `{Univalence} {X : Type} (hX : isFinSet X)
  (R : X -> X -> PropU)
  (rr : forall x, fst (R x x))
  (rs : forall x y, fst (R x y) -> fst (R y x))
  (rt : forall x y z, fst (R x y) -> fst (R y z) -> fst (R x z))
  (dR : forall x y, isDecidable (fst (R x y)))
  : isFinSet (quot R)
  := isFinSet_Eqv (quot_QuotHIT R rr rs rt)
       (Finite_isFinSet (@finite_quotient _ X (isFinSet_Finite hX)
                           (fun x y => fst (R x y))
                           (fun x y => isProp_IsHProp (snd (R x y)))
                           rr rt rs dR)).
