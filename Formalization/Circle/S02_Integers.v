(** * Section 3.2 The integers

    Part of Chapter 3 ([circle.tex]); see [Circle.v] for an overview of
    the chapter and [Symmetry.v] for the conventions.

    ** Summary of this formalization

    - [def:zet]: the higher inductive type [ℤ] with [ι₊ : ℕ → ℤ],
      [ι₋ : ℕ⁻ → ℤ] and [zeq : ι₋(-0) = ι₊(0)] is realized as the library's
      [Pushout] of [-0 : ℕ⁻] and [0 : ℕ] over [𝟙], with [ι₊ :≡ pushr],
      [ι₋ :≡ pushl], [zeq :≡ pglue(triv)]; the induction principle
      computes on [ι₊] and [ι₋] by definition, with the computation rule
      [ℤ_ind_zeq] for [zeq].
    - [ℤ] is a set with decidable equality, via an equivalence [ℤ ≃ Int]
      with the library's inductive integers.  Hence families of
      identifications in a set need no [zeq] case ([ℤ_ind_prop]).
    - Negation (an involution, with [ap_-(zeq) :≡ zeq⁻¹]), the successor
      [zs] (with [ap_s(zeq) :≡ refl_1]) and the predecessor, so that [zs]
      is an equivalence; the iteration [f^z] of any equivalence
      [f : X ≃ X] for [z : ℤ]; addition [z + y :≡ zs^y(z)], subtraction,
      the fact that they are mutually inverse, and multiplication
      [zy :≡ (w ↦ z + w)^y(0)].
    - Exercises [xca:addition-on-Z-and-N] and [xca:commutative-add-Z].
      These, and the inverse of [w ↦ z + w], are proved by comparing the
      operations with those of the library's [Int] ([toInt_zadd],
      [toInt_zmul]) and reusing its lemmas.
    - The order [z ≤ y :≡ ∑_n (y = z + ι₊(n))], which extends [≤] on [ℕ].
    - Left out: the alternative form of [ℤ]-induction (giving [f(0)],
      [g'] and [h']), a remark without a precise statement.
    - Numerals in patterns are written [O], since [0] in patterns refers
      to [trunc_index]. *)

From HoTT Require Import
  Basics Types.Sigma Types.Prod Types.Equiv Types.Bool Types.Universe
  Types.Forall Types.Paths Truncations.Core Colimits.Coeq Colimits.Pushout
  Spaces.Nat.Core Spaces.Int Spaces.Circle.
From SymmetryMirror Require Export Circle.S01_Circle.

Local Open Scope uf_scope.

(** ** 3.2 The integers *)

(** Definition [def:zet]: the higher inductive type [ℤ] with constructors
    [ι₊ : ℕ → ℤ], [ι₋ : ℕ⁻ → ℤ] and [zeq : ι₋(-0) = ι₊(0)] is the
    pushout of [-0 : ℕ⁻] and [0 : ℕ] over [𝟙], the library's [Pushout].
    Its induction principle computes on [ι₊] and [ι₋] by definition. *)
Definition ℤ : Type := Pushout (fun _ : True => negN 0%nat) (fun _ : True => 0%nat).

Definition iplus (n : ℕ) : ℤ := pushr n.
Definition iminus (m : NNN) : ℤ := pushl m.
Definition zeq : iminus (negN 0) = iplus 0 := pglue tt.

Definition ℤ_ind (T : ℤ -> Type) (g : forall n, T (iplus n))
  (h : forall m, T (iminus m)) (q : PathOver T zeq (h (negN 0)) (g 0%nat))
  : forall z, T z
  := Pushout_ind T h g (fun t => match t with tt => q end).

Definition ℤ_ind_plus T g h q n : ℤ_ind T g h q (iplus n) = g n := refl.
Definition ℤ_ind_minus T g h q m : ℤ_ind T g h q (iminus m) = h m := refl.
Definition ℤ_ind_zeq T g h q : apd (ℤ_ind T g h q) zeq = q
  := Pushout_ind_beta_pglue T h g _ tt.

Definition ℤ_rec (T : Type) (g : ℕ -> T) (h : NNN -> T) (q : h (negN 0) = g 0%nat)
  : ℤ -> T
  := Pushout_rec T h g (fun _ => q).

Definition ℤ_rec_zeq T g h q : ap (ℤ_rec T g h q) zeq = q
  := Pushout_rec_beta_pglue T h g _ tt.

(** [ℤ] is a set with decidable equality: it is equivalent to the
    library's inductive type [Int]. *)
Definition toInt : ℤ -> Int
  := ℤ_rec Int int_of_nat (fun m => int_neg (int_of_nat (unneg m))) refl.

Definition fromInt (x : Int) : ℤ
  := match x with
     | negS n => iminus (negN (S n))
     | zero => iplus 0
     | posS n => iplus (S n)
     end.

Definition toInt_fromInt (x : Int) : toInt (fromInt x) = x
  := match x with negS _ | zero | posS _ => refl end.

Definition fromInt_toInt (z : ℤ) : fromInt (toInt z) = z.
Proof.
  pose (g := fun n : ℕ => match n as n' return fromInt (toInt (iplus n')) = iplus n' with
                      | O => refl | S _ => refl end).
  pose (h := fun m : NNN => match m as m' return fromInt (toInt (iminus m')) = iminus m' with
                      | negN n =>
                          match n as n' return fromInt (toInt (iminus (negN n')))
                                               = iminus (negN n') with
                          | O => zeq⁻¹ | S _ => refl end
                      end).
  refine (ℤ_ind (fun z => fromInt (toInt z) = z) g h _ z).
  - refine (trp_paths_fg (fun z => fromInt (toInt z)) idmap zeq zeq⁻¹ @ _).
    refine (ap (fun r => (ap idmap zeq ⋅ zeq⁻¹) ⋅ r⁻¹)
              (ap_compose toInt fromInt zeq @ ap (ap fromInt) (ℤ_rec_zeq _ _ _ _)) @ _).
    refine (trans_1p _ @ _).
    exact (ap (fun r => r ⋅ zeq⁻¹) (ap_idmap zeq) @ trans_Vp zeq).
Defined.

Definition ℤ_Int : ℤ ≃ Int := mkEqv toInt fromInt fromInt_toInt toInt_fromInt.

Definition Int_isSet : isSet Int := IsHSet_isSet ishset_int.

Definition ℤ_isSet : isSet ℤ := is_ntype_Eqv 0 (Eqv_inv ℤ_Int) Int_isSet.

Definition toInt_inj {x y : ℤ} (e : toInt x = toInt y) : x = y
  := (fromInt_toInt x)^ @ ap fromInt e @ fromInt_toInt y.

Definition ℤ_isDecSet : isDecSet ℤ
  := hedberg (fun x y => match dec_paths (toInt x) (toInt y) with
                         | inl e => inl (toInt_inj e)
                         | inr n => inr (fun e => n (ap toInt e))
                         end).

(** Since [ℤ] is a set, families of identifications in [ℤ] (or in any
    set) need no loop case. *)
Definition ℤ_ind_prop (T : ℤ -> Type) (hT : forall z, isProp (T z))
  (g : forall n, T (iplus n)) (h : forall m, T (iminus m)) : forall z, T z
  := ℤ_ind T g h (hT _ _ _).

(** Negation, with [ap_-(zeq) :≡ zeq⁻¹]; it is its own inverse. *)
Definition zneg : ℤ -> ℤ
  := ℤ_rec ℤ (fun n => iminus (negN n)) (fun m => iplus (unneg m)) zeq⁻¹.

Definition zneg_zneg (z : ℤ) : zneg (zneg z) = z.
Proof.
  refine (ℤ_ind_prop _ (fun z => ℤ_isSet _ _) _ _ z).
  - intro n. exact refl.
  - intros [n]. exact refl.
Defined.

Definition znegEqv : ℤ ≃ ℤ := mkEqv zneg zneg zneg_zneg zneg_zneg.

(** The successor [zs], with [ap_s(zeq) :≡ refl_1], and the predecessor
    [zp], its inverse. *)
Definition zs : ℤ -> ℤ
  := ℤ_rec ℤ (fun n => iplus (S n))
       (fun m => match m with
                 | negN O => iplus 1
                 | negN (S n) => iminus (negN n)
                 end)
       refl.

Definition zp : ℤ -> ℤ
  := ℤ_rec ℤ (fun n => match n with O => iminus (negN 1) | S n => iplus n end)
       (fun m => iminus (negN (S (unneg m))))
       refl.

Definition zp_zs (z : ℤ) : zp (zs z) = z.
Proof.
  refine (ℤ_ind_prop _ (fun z => ℤ_isSet _ _) _ _ z).
  - intro n. exact refl.
  - intros [[|n]]; [exact zeq⁻¹ | exact refl].
Defined.

Definition zs_zp (z : ℤ) : zs (zp z) = z.
Proof.
  refine (ℤ_ind_prop _ (fun z => ℤ_isSet _ _) _ _ z).
  - intros [|n]; [exact zeq | exact refl].
  - intros [n]. exact refl.
Defined.

Definition zsEqv : ℤ ≃ ℤ := mkEqv zs zp zp_zs zs_zp.

(** The inverse of an equivalence built by [mkEqv] is the given one. *)
Definition eqinv_mkEqv {X Y : Type} (f : X -> Y) (g : Y -> X) gf fg (y : Y)
  : eqinv (snd (mkEqv f g gf fg)) y = g y
  := ap (eqinv (snd (mkEqv f g gf fg))) (fg y)^ @ eqinv_l _ (g y).

(** Iteration [f^z] of an equivalence [f : X ≃ X], for [z : ℤ]:
    [f^{ι₊(n)} :≡ f^n], [f^{ι₋(-n)} :≡ (f⁻¹)^n], and [f^0 ≡ id ≡ f^{-0}]. *)
Definition iterZ {X : Type} (f : X ≃ X) : ℤ -> X -> X
  := ℤ_rec (X -> X) (fun n => iter (fst f) n)
       (fun m => iter (eqinv (snd f)) (unneg m)) refl.

(** Addition [z + y :≡ zs^y(z)], subtraction [z - y :≡ z + (-y)]. *)
Definition zadd (z y : ℤ) : ℤ := iterZ zsEqv y z.
Definition zsub (z y : ℤ) : ℤ := zadd z (zneg y).

(** Comparison of the operations with those of the library's [Int]. *)
Definition toInt_zs (x : ℤ) : toInt (zs x) = int_succ (toInt x).
Proof.
  refine (ℤ_ind_prop _ (fun _ => Int_isSet _ _) _ _ x).
  - intros [|n]; exact refl.
  - intros [[|[|n]]]; exact refl.
Defined.

Definition toInt_zp (x : ℤ) : toInt (zp x) = int_pred (toInt x).
Proof.
  refine (ℤ_ind_prop _ (fun _ => Int_isSet _ _) _ _ x).
  - intros [|[|n]]; exact refl.
  - intros [[|n]]; exact refl.
Defined.

Definition toInt_zneg (x : ℤ) : toInt (zneg x) = int_neg (toInt x).
Proof.
  refine (ℤ_ind_prop _ (fun _ => Int_isSet _ _) _ _ x).
  - intro n. exact refl.
  - intros [[|n]]; exact refl.
Defined.

Definition int_pred_neg (n : ℕ)
  : int_pred (int_neg (int_of_nat n)) = int_neg (int_of_nat (S n))
  := match n with O => refl | S _ => refl end.

Definition toInt_zadd (z y : ℤ) : toInt (zadd z y) = int_add (toInt z) (toInt y).
Proof.
  refine (ℤ_ind_prop _ (fun _ => Int_isSet _ _) _ _ y).
  - intro n. change (toInt (iter zs n z) = int_add (toInt z) (int_of_nat n)).
    induction n as [|n IH].
    + exact (int_add_0_r _)^.
    + exact (toInt_zs _ @ ap int_succ IH @ (int_add_succ_r _ _)^
             @ ap (int_add (toInt z)) (int_nat_succ n)).
  - intros [n].
    change (toInt (iter (eqinv (snd zsEqv)) n z)
            = int_add (toInt z) (int_neg (int_of_nat n))).
    induction n as [|n IH].
    + exact (int_add_0_r _)^.
    + exact (ap toInt (eqinv_mkEqv zs zp zp_zs zs_zp _) @ toInt_zp _
             @ ap int_pred IH @ (int_add_pred_r _ _)^
             @ ap (int_add (toInt z)) (int_pred_neg n)).
Defined.

(** Exercise [xca:addition-on-Z-and-N], for addition. *)
Definition iplus_add (n m : ℕ) : iplus (add n m) = zadd (iplus n) (iplus m)
  := toInt_inj (x := iplus (add n m)) ((int_nat_add m n)^ @ int_add_comm _ _ @ (toInt_zadd (iplus n) (iplus m))^).

(** Addition and subtraction are mutually inverse. *)
Definition zsub_zadd (w z : ℤ) : zsub (zadd w z) z = w.
Proof.
  apply toInt_inj. unfold zsub.
  refine (toInt_zadd _ _ @ ap011 int_add (toInt_zadd _ _) (toInt_zneg _) @ _).
  exact ((int_add_assoc _ _ _)^ @ ap (int_add (toInt w)) (int_add_neg_r _)
         @ int_add_0_r _).
Defined.

Definition zadd_zsub (w z : ℤ) : zadd (zsub w z) z = w.
Proof.
  apply toInt_inj. unfold zsub.
  refine (toInt_zadd _ _ @ ap (fun t => int_add t (toInt z))
            (toInt_zadd _ _ @ ap (int_add (toInt w)) (toInt_zneg _)) @ _).
  exact ((int_add_assoc _ _ _)^ @ ap (int_add (toInt w)) (int_add_neg_l _)
         @ int_add_0_r _).
Defined.

(** Hence [w ↦ z + w] is an equivalence, which we iterate to define
    multiplication [zy :≡ (w ↦ z + w)^y(0)]. *)
Definition zaddEqv (z : ℤ) : ℤ ≃ ℤ.
Proof.
  refine (mkEqv (zadd z) (fun w => fromInt (int_add (int_neg (toInt z)) (toInt w))) _ _).
  - intro w. refine (_ @ fromInt_toInt w). apply ap.
    exact (ap (int_add _) (toInt_zadd z w) @ int_add_assoc _ _ _
           @ ap (fun t => int_add t (toInt w)) (int_add_neg_l _)).
  - intro w. apply toInt_inj.
    exact (toInt_zadd _ _ @ ap (int_add (toInt z)) (toInt_fromInt _)
           @ int_add_assoc _ _ _
           @ ap (fun t => int_add t (toInt w)) (int_add_neg_r _)).
Defined.

Definition zmul (z y : ℤ) : ℤ := iterZ (zaddEqv z) y (iplus 0).

Definition toInt_zmul (z y : ℤ) : toInt (zmul z y) = int_mul (toInt z) (toInt y).
Proof.
  refine (ℤ_ind_prop _ (fun _ => Int_isSet _ _) _ _ y).
  - intro n. change (toInt (iter (zadd z) n (iplus 0)) = int_mul (toInt z) (int_of_nat n)).
    induction n as [|n IH].
    + exact (int_mul_0_r _)^.
    + exact (toInt_zadd _ _ @ ap (int_add (toInt z)) IH @ (int_mul_succ_r _ _)^
             @ ap (int_mul (toInt z)) (int_nat_succ n)).
  - intros [n].
    change (toInt (iter (eqinv (snd (zaddEqv z))) n (iplus 0))
            = int_mul (toInt z) (int_neg (int_of_nat n))).
    induction n as [|n IH].
    + exact (int_mul_0_r _)^.
    + exact (ap toInt (eqinv_mkEqv (zadd z)
                         (fun w => fromInt (int_add (int_neg (toInt z)) (toInt w))) _ _ _)
             @ toInt_fromInt _
             @ ap (int_add (int_neg (toInt z))) IH @ (int_mul_pred_r _ _)^
             @ ap (int_mul (toInt z)) (int_pred_neg n)).
Defined.

(** Exercise [xca:addition-on-Z-and-N], for multiplication. *)
Definition iplus_mul (n m : ℕ) : iplus (mul n m) = zmul (iplus n) (iplus m)
  := toInt_inj (x := iplus (mul n m)) ((int_nat_mul n m)^ @ (toInt_zmul (iplus n) (iplus m))^).

(** Exercise [xca:commutative-add-Z]. *)
Definition zadd_comm (x y : ℤ) : zadd x y = zadd y x
  := toInt_inj (toInt_zadd x y @ int_add_comm _ _ @ (toInt_zadd y x)^).

Definition zmul_comm (x y : ℤ) : zmul x y = zmul y x
  := toInt_inj (toInt_zmul x y @ int_mul_comm _ _ @ (toInt_zmul y x)^).

(** The order [z ≤ y :≡ ∑_{n:ℕ} (y = z + ι₊(n))] extends the order on [ℕ]. *)
Definition zle (z y : ℤ) : Type := {n : ℕ & y = zadd z (iplus n)}.

Definition nat_of_int (x : Int) : ℕ
  := match x with posS n => S n | _ => 0%nat end.

Definition iplus_inj {n m : ℕ} (e : iplus n = iplus m) : n = m.
Proof.
  pose (c := fun k : ℕ => match k as k' return nat_of_int (toInt (iplus k')) = k' with
                          | O => refl | S _ => refl end).
  exact ((c n)^ @ ap (fun z => nat_of_int (toInt z)) e @ c m).
Defined.

Definition le_zle (m n : ℕ)
  : (le m n -> zle (iplus m) (iplus n)) × (zle (iplus m) (iplus n) -> le m n).
Proof.
  refine (_; _).
  - intros [k e]. exact (k; ap iplus (e^ @ add_comm k m) @ iplus_add m k).
  - intros [k e]. exact (k; add_comm k m @ iplus_inj (iplus_add m k @ e^)).
Defined.
