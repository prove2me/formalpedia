-- Prove2me | solution 1 for AnalyticCombinatorics.Ch1.CombClass.egf_set
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-25T09:35:03.613009+00:00
-- url     : https://prove2.me/submissions/15cc8bff-74bd-483f-94bf-548a8f98194b

import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledProduct
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSetOde
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Ch2 §II.1 — Labelled structures and exponential generating functions

Flajolet & Sedgewick, Part A, Chapter II. A *labelled* class is again a graded
family of finite types (we reuse `CombClass`), but is enumerated by its
*exponential* generating function (EGF)

  `A(z) = ∑ₙ Aₙ zⁿ/n!`.

This file defines the EGF and two foundational flagships:
- permutations (`Perm (Fin n)`, `Aₙ = n!`) with EGF `1/(1 - z)`;
- the "set" class (one object of each size) with EGF `e^z`.

The labelled product (the defining feature of EGFs) is developed separately.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

@[simp] lemma coeff_egfSeq (a : ℕ → ℕ) (n : ℕ) :
    coeff n (egfSeq a) = (a n : ℚ) / (n.factorial : ℚ) := by
  rw [egfSeq, coeff_mk]

@[simp] lemma CombClass.coeff_egf (C : CombClass) (n : ℕ) :
    coeff n C.egf = (C.counts n : ℚ) / (n.factorial : ℚ) := by
  rw [CombClass.egf, coeff_egfSeq]

end AnalyticCombinatorics.Ch1

/-!
# Ch2 §II.1 — The labelled product

Flajolet & Sedgewick, Part A, Chapter II, the labelled (partitional) product, the
defining construction of the EGF framework. To form `A ⋆ B` on `n` labels, one
chooses which `k` of the labels go to the `A`-component (a `k`-subset) and puts an
`A`-structure on them and a `B`-structure on the remaining `n-k`. Hence

  `(A ⋆ B)ₙ = ∑_{k} C(n,k) · Aₖ · B_{n-k}`   (binomial convolution),

and therefore the EGFs multiply:

  **`(A ⋆ B)(z) = A(z) · B(z)`**   (F&S Theorem II.1).
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

/-- Counting sequences convolve binomially: `(A ⋆ B)ₙ = ∑_k C(n,k)·Aₖ·B_{n-k}`. -/
@[simp] lemma CombClass.counts_lprod (A B : CombClass) (n : ℕ) :
    (A.lprod B).counts n
      = ∑ k : Fin (n + 1), n.choose k * A.counts k * B.counts (n - k) := by
  change Fintype.card
      (Σ k : Fin (n + 1), { S : Finset (Fin n) // S.card = k } × A.Obj k × B.Obj (n - k)) = _
  rw [Fintype.card_sigma]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_finset_len, Fintype.card_fin]
  simp only [CombClass.counts]
  ring

/-- **Labelled product rule** (F&S Theorem II.1): `(A ⋆ B)(z) = A(z)·B(z)`. -/
theorem CombClass.egf_lprod (A B : CombClass) :
    (A.lprod B).egf = A.egf * B.egf := by
  ext n
  rw [CombClass.coeff_egf, CombClass.counts_lprod, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Fin.sum_univ_eq_sum_range
      (fun k => n.choose k * A.counts k * B.counts (n - k)) (n + 1),
    Nat.cast_sum, div_eq_iff (by exact_mod_cast Nat.factorial_ne_zero n), Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range, Nat.lt_succ_iff] at hk
  have hk' : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hnk' : ((n - k).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n - k)
  rw [CombClass.coeff_egf, CombClass.coeff_egf]
  field_simp
  rw [← Nat.choose_mul_factorial_mul_factorial hk]
  push_cast
  ring

end AnalyticCombinatorics.Ch1

/-!
# Ch2 §II.2 — The labelled set construction SET(C): counts layer

Flajolet & Sedgewick, Part A, Chapter II. `SET(C)` forms *sets* of labelled
C-objects (`C₀=∅`): a set partition of the `n` labels into blocks, each block
carrying a C-structure on its labels. Hence

  `SET(C)ₙ = ∑_{π : set partition of [n]} ∏_{B∈π} C_{|B|}`   (exponential formula),

and the EGF is `exp(C(z))`. This file builds the graded `Fintype` model and the
counting identity; the EGF identity is developed separately.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- The counting identity for `SET(C)`: `SET(C)ₙ = ∑_π ∏_{B∈π} C_{|B|}`, from
`card_sigma`/`card_pi`. -/
lemma CombClass.counts_set (C : CombClass) (n : ℕ) :
    C.set.counts n
      = ∑ π : Finpartition (Finset.univ : Finset (Fin n)),
          ∏ B : π.parts, C.counts (B.val.card) := by
  classical
  change Fintype.card
      (Σ π : Finpartition (Finset.univ : Finset (Fin n)), ∀ B : π.parts, C.Obj (B.val.card)) = _
  rw [Fintype.card_sigma]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [Fintype.card_pi]
  rfl

end AnalyticCombinatorics.Ch1

/-!
# Ch2 §II.2 — ODE machinery for the labelled set construction

Toward the labelled set transfer `SET(C)(z) = exp(C(z))` (F&S §II.2). The strategy
(differential route): `exp(C(z))` and `SET(C)(z)` both satisfy the linear ODE
`F' = C'(z)·F` with constant term `1`, and that ODE has a unique solution. This file
proves the two *general* (combinatorics-free) ingredients:

* `subst_exp_ode` — `exp(C(z)) := (exp ℚ).subst C.egf` satisfies `F' = C'·F`
  (the chain rule `derivative_subst` + `derivative_exp`).
* `ode_unique` — a power series with `H' = G·H` and `H(0) = 0` is `0`.

The remaining (combinatorial) ingredient — that `SET(C).egf` satisfies the same ODE,
via a pointing bijection on set partitions — is developed separately.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- `exp(C(z))` (substituting `C.egf` for `X` in `e^X`) is a valid substitution when
`C₀ = ∅`. -/
lemma CombClass.hasSubst_egf {C : CombClass} (hC : C.counts 0 = 0) :
    HasSubst C.egf := by
  apply HasSubst.of_constantCoeff_zero'
  rw [← coeff_zero_eq_constantCoeff_apply, CombClass.coeff_egf, hC]
  simp

/-- `exp(C(z))` satisfies the linear ODE `F' = C'(z)·F`. -/
theorem CombClass.subst_exp_ode {C : CombClass} (hC : C.counts 0 = 0) :
    d⁄dX ℚ ((exp ℚ).subst C.egf) = d⁄dX ℚ C.egf * (exp ℚ).subst C.egf := by
  set_option backward.isDefEq.respectTransparency false in
    rw [derivative_subst (hg := CombClass.hasSubst_egf hC), derivative_exp]
    ring

/-- **ODE uniqueness**: a power series solving `H' = G·H` with vanishing constant term
is `0` (coefficient induction). -/
theorem ode_unique {R : Type*} [CommSemiring R] [Algebra ℚ R] {H G : R⟦X⟧}
    (hode : d⁄dX R H = G * H)
    (h0 : constantCoeff H = 0) : H = 0 := by
  have key : ∀ n, coeff n H = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      match n with
      | 0 => rw [coeff_zero_eq_constantCoeff_apply]; exact h0
      | m + 1 =>
        have hd := congrArg (coeff m) hode
        rw [coeff_derivative, coeff_mul,
          Finset.sum_eq_zero (fun p hp => ?_)] at hd
        · have hu : IsUnit ((m : R) + 1) := by
            simpa using
              (IsUnit.map (algebraMap ℚ R)
                (isUnit_iff_ne_zero.mpr (by positivity : ((m : ℚ) + 1) ≠ 0)))
          exact hu.mul_left_eq_zero.mp hd
        · rw [Finset.mem_antidiagonal] at hp
          rw [ih p.2 (by omega), mul_zero]
  ext n
  rw [key n, map_zero]

end AnalyticCombinatorics.Ch1

/-!
# Ch2 §II.2 — The labelled set ODE

This file contains the coefficient-level machinery for the differential equation
of the labelled set construction.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

lemma labelledSetObj_card (C : CombClass) (α : Type*) [Fintype α] [DecidableEq α] :
    Fintype.card (labelledSetObj C α) = C.set.counts (Fintype.card α) := by
  rw [← labelledSetObj_fin_card C (Fintype.card α)]
  exact Fintype.card_congr (labelledSetObjCongr C (Fintype.equivFin α))

lemma labelledSetObj_card_eq_setWeightFull (C : CombClass) (α : Type*) [Fintype α]
    [DecidableEq α] :
    Fintype.card (labelledSetObj C α) = setWeightFull C α := by
  change Fintype.card
      (Σ P : Finpartition (Finset.univ : Finset α), ∀ B : P.parts, C.Obj B.val.card) = _
  rw [Fintype.card_sigma]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [Fintype.card_pi]
  rfl

lemma setWeightFull_card (C : CombClass) (α : Type*) [Fintype α] [DecidableEq α] :
    setWeightFull C α = C.set.counts (Fintype.card α) := by
  rw [← labelledSetObj_card_eq_setWeightFull, labelledSetObj_card]

lemma prod_parts_sdiffSubtype (C : CombClass) {α : Type*} [Fintype α] [DecidableEq α]
    (B : Finset α) (Q : Finpartition ((Finset.univ : Finset α) \ B)) :
    (∏ A : (finpartitionSdiffSubtype B Q).parts, C.counts A.val.card) =
      ∏ A : Q.parts, C.counts A.val.card := by
  rw [Finset.prod_coe_sort (finpartitionSdiffSubtype B Q).parts
      (fun A : Finset {x : α // x ∉ B} => C.counts A.card),
    Finset.prod_coe_sort Q.parts (fun A : Finset α => C.counts A.card)]
  simp only [finpartitionSdiffSubtype, Finpartition.ofExistsUnique_parts]
  have hinj : ∀ A ∈ Q.parts, ∀ D ∈ Q.parts,
      A.subtype (fun x => x ∉ B) = D.subtype (fun x => x ∉ B) → A = D := by
    intro A hA D hD hsub
    ext x
    constructor
    · intro hx
      have hxnot : x ∉ B := by
        have hxcomp : x ∈ (Finset.univ : Finset α) \ B := Q.subset hA hx
        simpa using hxcomp
      have hxsub : (⟨x, hxnot⟩ : {x : α // x ∉ B}) ∈ A.subtype (fun x => x ∉ B) := by
        simpa using hx
      rw [hsub] at hxsub
      simpa using hxsub
    · intro hx
      have hxnot : x ∉ B := by
        have hxcomp : x ∈ (Finset.univ : Finset α) \ B := Q.subset hD hx
        simpa using hxcomp
      have hxsub : (⟨x, hxnot⟩ : {x : α // x ∉ B}) ∈ D.subtype (fun x => x ∉ B) := by
        simpa using hx
      rw [← hsub] at hxsub
      simpa using hxsub
  rw [Finset.prod_image hinj]
  refine Finset.prod_congr rfl fun A hA => ?_
  have hmap : (A.subtype (fun x => x ∉ B)).map
      (Function.Embedding.subtype fun x : α => x ∉ B) = A :=
    Finset.subtype_map_of_mem (fun x hx => by
      have hxcomp : x ∈ (Finset.univ : Finset α) \ B := Q.subset hA hx
      simpa using hxcomp)
  have hcard : (A.subtype (fun x => x ∉ B)).card = A.card := by
    rw [← Finset.card_map (Function.Embedding.subtype fun x : α => x ∉ B), hmap]
  rw [hcard]

lemma setWeightFinset_sdiff_eq_setWeightFull (C : CombClass) {α : Type*}
    [Fintype α] [DecidableEq α] (B : Finset α) :
    setWeightFinset C ((Finset.univ : Finset α) \ B) =
      setWeightFull C {x : α // x ∉ B} := by
  unfold setWeightFinset setWeightFull
  exact Fintype.sum_equiv (finpartitionSdiffSubtypeCongr B)
    (fun Q : Finpartition ((Finset.univ : Finset α) \ B) =>
      ∏ A : Q.parts, C.counts A.val.card)
    (fun Q : Finpartition (Finset.univ : Finset {x : α // x ∉ B}) =>
      ∏ A : Q.parts, C.counts A.val.card)
    (fun Q => (prod_parts_sdiffSubtype C B Q).symm)

lemma prod_parts_eq_root_mul_avoid (C : CombClass) {α : Type*} [DecidableEq α]
    {s B : Finset α} {P : Finpartition s} (hB : B ∈ P.parts) :
    (∏ A : P.parts, C.counts A.val.card) =
      C.counts B.card * ∏ A : (P.avoid B).parts, C.counts A.val.card := by
  rw [Finset.prod_coe_sort P.parts (fun A : Finset α => C.counts A.card),
    Finset.prod_coe_sort (P.avoid B).parts (fun A : Finset α => C.counts A.card)]
  have hparts : P.parts = insert B (P.avoid B).parts := by
    ext A
    by_cases hAB : A = B
    · subst hAB
      simp [Finpartition.mem_avoid_of_mem_part hB, hB]
    · simp [Finpartition.mem_avoid_of_mem_part hB, hAB]
  have hBnot : B ∉ (P.avoid B).parts := by
    simp [Finpartition.mem_avoid_of_mem_part hB]
  rw [hparts, Finset.prod_insert hBnot]

lemma setWeightFull_root (C : CombClass) {α : Type*} [Fintype α] [DecidableEq α]
    (r : α) :
    setWeightFull C α =
      ∑ B : {B : Finset α // r ∈ B},
        C.counts B.val.card * setWeightFull C {x : α // x ∉ B.val} := by
  classical
  unfold setWeightFull
  let block : Finpartition (Finset.univ : Finset α) → {B : Finset α // r ∈ B} :=
    fun P => ⟨P.part r, by simpa using P.mem_part (by simp)⟩
  let w : Finpartition (Finset.univ : Finset α) → ℕ :=
    fun P => ∏ A : P.parts, C.counts A.val.card
  have hsplit :
      ∑ P : Finpartition (Finset.univ : Finset α), w P =
        ∑ x : (Σ B : {B : Finset α // r ∈ B}, {P // block P = B}), w x.2.val := by
    symm
    exact Fintype.sum_equiv (Equiv.sigmaFiberEquiv block)
      (fun x : (Σ B : {B : Finset α // r ∈ B}, {P // block P = B}) => w x.2.val)
      w
      (by intro x; rfl)
  rw [hsplit, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun B _ => ?_
  let fiberEquiv :
      {P : Finpartition (Finset.univ : Finset α) // block P = B} ≃
        {P : Finpartition (Finset.univ : Finset α) // P.part r = B.val} :=
    { toFun := fun P => ⟨P.val, by
        have h := congrArg Subtype.val P.property
        exact h⟩
      invFun := fun P => ⟨P.val, by
        apply Subtype.ext
        exact P.property⟩
      left_inv := by
        intro P
        apply Subtype.ext
        rfl
      right_inv := by
        intro P
        apply Subtype.ext
        rfl }
  let rootEquiv := finpartitionRootFiberEquiv r B.property
  have hfiber :
      ∑ P : {P : Finpartition (Finset.univ : Finset α) // block P = B}, w P.val =
        ∑ Q : Finpartition ((Finset.univ : Finset α) \ B.val),
          C.counts B.val.card * ∏ A : Q.parts, C.counts A.val.card := by
    calc
      ∑ P : {P : Finpartition (Finset.univ : Finset α) // block P = B}, w P.val
          = ∑ P : {P : Finpartition (Finset.univ : Finset α) // P.part r = B.val},
              w P.val := by
            exact Fintype.sum_equiv fiberEquiv
              (fun P => w P.val) (fun P => w P.val) (by intro P; rfl)
      _ = ∑ Q : Finpartition ((Finset.univ : Finset α) \ B.val),
              w ((rootEquiv.symm Q).val) := by
            exact Fintype.sum_equiv rootEquiv
              (fun P => w P.val)
              (fun Q => w ((rootEquiv.symm Q).val))
              (by intro P; simp)
      _ = ∑ Q : Finpartition ((Finset.univ : Finset α) \ B.val),
              C.counts B.val.card * ∏ A : Q.parts, C.counts A.val.card := by
            refine Finset.sum_congr rfl fun Q _ => ?_
            have hruniv : r ∈ (Finset.univ : Finset α) := by simp
            have hBmem : B.val ∈ (rootEquiv.symm Q).val.parts := by
              have hprop := (rootEquiv.symm Q).property
              simpa [hprop] using (rootEquiv.symm Q).val.part_mem.2 hruniv
            change (∏ A : (rootEquiv.symm Q).val.parts, C.counts A.val.card) =
              C.counts B.val.card * ∏ A : Q.parts, C.counts A.val.card
            rw [prod_parts_eq_root_mul_avoid C hBmem]
            have havoid : (rootEquiv.symm Q).val.avoid B.val = Q := by
              exact Equiv.apply_symm_apply rootEquiv Q
            rw [havoid]
  rw [hfiber]
  rw [← Finset.mul_sum]
  change C.counts B.val.card * setWeightFinset C ((Finset.univ : Finset α) \ B.val) =
    C.counts B.val.card * setWeightFull C {x : α // x ∉ B.val}
  rw [setWeightFinset_sdiff_eq_setWeightFull]

@[simp] lemma rootBlockEquiv_card (n : ℕ) (S : Finset (Fin n)) :
    (rootBlockEquiv n S).val.card = S.card + 1 := by
  simp [rootBlockEquiv]

lemma rootBlockEquiv_compl_card (n : ℕ) (S : Finset (Fin n)) :
    Fintype.card {x : Fin (n + 1) // x ∉ (rootBlockEquiv n S).val} = n - S.card := by
  rw [Fintype.card_subtype]
  have hset : ({x | x ∉ (rootBlockEquiv n S).val} : Finset (Fin (n + 1))) =
      (Finset.univ : Finset (Fin (n + 1))) \ (rootBlockEquiv n S).val := by
    ext x
    simp
  rw [hset, Finset.card_sdiff_of_subset (by simp), Finset.card_univ, Fintype.card_fin,
    rootBlockEquiv_card]
  omega

lemma sum_finset_by_card (n : ℕ) (f : ℕ → ℕ) :
    (∑ S : Finset (Fin n), f S.card) =
      ∑ k : Fin (n + 1), n.choose (k : ℕ) * f (k : ℕ) := by
  classical
  let len : Finset (Fin n) → Fin (n + 1) := fun S =>
    ⟨S.card, by
      exact Nat.lt_succ_of_le (by simpa [Fintype.card_fin] using S.card_le_univ)⟩
  have hsplit :
      (∑ S : Finset (Fin n), f S.card) =
        ∑ x : (Σ k : Fin (n + 1), {S : Finset (Fin n) // len S = k}), f x.2.val.card := by
    symm
    exact Fintype.sum_equiv (Equiv.sigmaFiberEquiv len)
      (fun x : (Σ k : Fin (n + 1), {S : Finset (Fin n) // len S = k}) =>
        f x.2.val.card)
      (fun S : Finset (Fin n) => f S.card)
      (by intro x; rfl)
  rw [hsplit, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hcard :
      Fintype.card {S : Finset (Fin n) // len S = k} = n.choose (k : ℕ) := by
    have hcard' :
        Fintype.card {S : Finset (Fin n) // len S = k} =
          (Fintype.card (Fin n)).choose (k : ℕ) := by
      rw [← Fintype.card_finset_len (α := Fin n) (k := (k : ℕ))]
      exact Fintype.card_congr
        { toFun := fun S => ⟨S.val, by
            have h := congrArg Fin.val S.property
            exact h⟩
          invFun := fun S => ⟨S.val, by
            apply Fin.ext
            exact S.property⟩
          left_inv := by intro S; apply Subtype.ext; rfl
          right_inv := by intro S; apply Subtype.ext; rfl }
    simpa [Fintype.card_fin] using hcard'
  trans Fintype.card {S : Finset (Fin n) // len S = k} * f (k : ℕ)
  · rw [← Finset.card_univ, Finset.sum_eq_card_nsmul]
    · rw [nsmul_eq_mul]
      refine congrArg (fun m => m * f (k : ℕ)) rfl
    · intro S _hS
      have h := congrArg Fin.val S.property
      simpa using congrArg f h
  · rw [hcard]

lemma CombClass.counts_set_succ (C : CombClass) (n : ℕ) :
    C.set.counts (n + 1)
      = ∑ i : Fin (n + 1),
          n.choose (i : ℕ) * C.counts ((i : ℕ) + 1) *
            C.set.counts (n - (i : ℕ)) := by
  classical
  conv_lhs => rw [show n + 1 = Fintype.card (Fin (n + 1)) by simp]
  rw [← setWeightFull_card C (Fin (n + 1))]
  rw [setWeightFull_root C (Fin.last n)]
  have hblocks :
      (∑ B : {B : Finset (Fin (n + 1)) // Fin.last n ∈ B},
          C.counts B.val.card * setWeightFull C {x : Fin (n + 1) // x ∉ B.val})
        =
      ∑ S : Finset (Fin n),
        C.counts (S.card + 1) * C.set.counts (n - S.card) := by
    symm
    exact Fintype.sum_equiv (rootBlockEquiv n)
      (fun S : Finset (Fin n) =>
        C.counts (S.card + 1) * C.set.counts (n - S.card))
      (fun B : {B : Finset (Fin (n + 1)) // Fin.last n ∈ B} =>
        C.counts B.val.card * setWeightFull C {x : Fin (n + 1) // x ∉ B.val})
      (by
        intro S
        change C.counts (S.card + 1) * C.set.counts (n - S.card) =
          C.counts ((rootBlockEquiv n S).val.card) *
            setWeightFull C {x : Fin (n + 1) // x ∉ (rootBlockEquiv n S).val}
        rw [rootBlockEquiv_card, setWeightFull_card,
          rootBlockEquiv_compl_card])
  rw [hblocks]
  rw [sum_finset_by_card n (fun k => C.counts (k + 1) * C.set.counts (n - k))]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Nat.mul_assoc]

/-- The EGF of the derivative class is the formal derivative of the EGF. -/
theorem CombClass.egf_deriv (C : CombClass) :
    C.deriv.egf = d⁄dX ℚ C.egf := by
  ext n
  rw [CombClass.coeff_egf, CombClass.counts_deriv, coeff_derivative,
    CombClass.coeff_egf]
  have hn : ((n + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hnf : ((n.factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp [Nat.factorial_succ, hn, hnf]
  rw [Nat.factorial_succ]
  push_cast
  ring_nf

/-- The pointed SET recurrence is exactly the labelled product `C' ⋆ SET(C)`. -/
theorem CombClass.egf_set_deriv_lprod (C : CombClass) :
    C.set.deriv.egf = (C.deriv.lprod C.set).egf := by
  ext n
  rw [CombClass.coeff_egf, CombClass.counts_deriv, CombClass.counts_set_succ,
    CombClass.coeff_egf, CombClass.counts_lprod]
  simp [CombClass.counts_deriv]

/-- The labelled SET construction satisfies `SET(C)' = C' * SET(C)`. -/
theorem CombClass.egf_set_ode (C : CombClass) :
    d⁄dX ℚ C.set.egf = d⁄dX ℚ C.egf * C.set.egf := by
  calc
    d⁄dX ℚ C.set.egf = C.set.deriv.egf := (CombClass.egf_deriv C.set).symm
    _ = (C.deriv.lprod C.set).egf := CombClass.egf_set_deriv_lprod C
    _ = C.deriv.egf * C.set.egf := CombClass.egf_lprod C.deriv C.set
    _ = d⁄dX ℚ C.egf * C.set.egf := by rw [CombClass.egf_deriv C]

end AnalyticCombinatorics.Ch1

/-!
# Ch2 §II.2 — The labelled set exponential formula

This file closes the labelled SET construction:
`SET(C)(z) = exp(C(z))` when `C` has no size-zero objects.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

lemma CombClass.counts_set_zero (C : CombClass) : C.set.counts 0 = 1 := by
  classical
  rw [CombClass.counts_set]
  have huniv : (Finset.univ : Finset (Fin 0)) = (⊥ : Finset (Fin 0)) := by
    simp
  rw [huniv]
  rw [Fintype.sum_unique]
  simp

end AnalyticCombinatorics.Ch1

open AnalyticCombinatorics AnalyticCombinatorics.Ch1
open PowerSeries
theorem solution (C : CombClass) (hC : C.counts 0 = 0) :
    C.set.egf = (PowerSeries.exp ℚ).subst C.egf := by
  let H : ℚ⟦X⟧ := C.set.egf - (PowerSeries.exp ℚ).subst C.egf
  have hode : d⁄dX ℚ H = d⁄dX ℚ C.egf * H := by
    dsimp [H]
    rw [map_sub, CombClass.egf_set_ode, CombClass.subst_exp_ode hC]
    set_option backward.isDefEq.respectTransparency false in
      ring
  have h0C : constantCoeff C.egf = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, CombClass.coeff_egf, hC]
    simp
  have h0set : constantCoeff C.set.egf = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, CombClass.coeff_egf,
      CombClass.counts_set_zero]
    simp
  have h0subst : constantCoeff ((PowerSeries.exp ℚ).subst C.egf) = 1 := by
    change MvPowerSeries.constantCoeff (PowerSeries.subst C.egf (PowerSeries.exp ℚ)) = 1
    rw [constantCoeff_subst (CombClass.hasSubst_egf hC)]
    rw [finsum_eq_single _ 0]
    · simp
    · intro d hd
      have hpow : MvPowerSeries.constantCoeff (C.egf ^ d) = 0 := by
        change constantCoeff (C.egf ^ d) = 0
        rw [map_pow, h0C, zero_pow hd]
      set_option backward.isDefEq.respectTransparency false in
        rw [hpow, smul_zero]
  have h0 : constantCoeff H = 0 := by
    dsimp [H]
    rw [map_sub, h0set, h0subst, sub_self]
  have hH : H = 0 := ode_unique hode h0
  exact sub_eq_zero.mp hH
