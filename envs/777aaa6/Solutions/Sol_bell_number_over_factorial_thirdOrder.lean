-- Prove2me | solution 1 for bell_number_over_factorial_thirdOrder
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-26T16:53:55.759077+00:00
-- url     : https://prove2.me/submissions/518004b9-3755-43d3-82c2-aa72f5d846e7

import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledProduct
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSetOde
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_SubstComp
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Exp
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_GaussianMoments
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_BellThirdOrder
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Fintype.Card
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Analysis.SpecialFunctions.Stirling

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Ch1 §I.2 / §I.3 — The sequence construction and integer compositions

Flajolet & Sedgewick, Part A, Chapter I. The sequence construction `SEQ(C)` forms
all finite sequences `(γ₁, …, γₘ)` of `C`-objects, with size the sum of the
component sizes. For this to give a (finite) combinatorial class one needs `C` to
have no object of size `0` (F&S's standing side-condition); the positive
component sizes of a size-`n` sequence then form a *composition* of `n`, so we
model `SEQ(C)` over Mathlib's `Composition n`.

This file proves, at the level of counting sequences, the genuine combinatorial
content:

* `counts_seq` — `(SEQ C)ₙ = ∑_{compositions c of n} ∏ᵢ C_{cᵢ}`.
* `counts_seq_posInt` — **integer compositions are sequences of positive
  integers** (F&S §I.3): `(SEQ ℙ)ₙ = #(Composition n) = 2^{n-1}`.

The closed-form generating function of compositions lives in `Compositions.lean`.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

@[simp] lemma CombClass.counts_posInt (n : ℕ) :
    CombClass.posInt.counts n = if 0 < n then 1 else 0 :=
  Fintype.card_fin _

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

theorem CombClass.egf_set (C : CombClass) (hC : C.counts 0 = 0) :
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

end AnalyticCombinatorics.Ch1

/-!
# Ch2 §II.3 — Applications of the labelled symbolic method

Flajolet & Sedgewick, Part A, Chapter II, §II.3. Using the labelled set and
sequence transfers on the positive-integer ("urn"/nonempty-block) class `ℙ`
(one object of each size `n ≥ 1`, EGF `e^z - 1`):

* set partitions / **Bell numbers** `SET(ℙ)`, EGF `exp(e^z - 1)`;
* **surjections** `SEQ(ℙ)`, EGF `1/(2 - e^z)`.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- The EGF of the positive-integer (nonempty-block) class is `e^z - 1`. -/
theorem CombClass.egf_posInt : CombClass.posInt.egf = PowerSeries.exp ℚ - 1 := by
  ext n
  rw [CombClass.coeff_egf, CombClass.counts_posInt, map_sub, coeff_exp, coeff_one]
  rcases n with _ | m <;> simp

/-- **Set partitions / Bell numbers** (F&S §II.3): `SET(ℙ)(z) = exp(e^z - 1)`. -/
theorem CombClass.egf_bell :
    CombClass.posInt.set.egf = (PowerSeries.exp ℚ).subst (PowerSeries.exp ℚ - 1) := by
  rw [CombClass.egf_set _ (by simp [CombClass.counts_posInt]), CombClass.egf_posInt]

end AnalyticCombinatorics.Ch1

open Filter ENNReal
open scoped PowerSeries Topology NNReal ENNReal

noncomputable section

namespace PowerSeries

@[simp] lemma coeff_toFMLS (f : PowerSeries ℂ) (n : ℕ) :
    (toFMLS f).coeff n = PowerSeries.coeff (R := ℂ) n f := by
  simp [toFMLS]

end PowerSeries
end

open Complex
open scoped NNReal ENNReal

noncomputable section

theorem coeff_eq_cauchy_circleIntegral_of_hasFPowerSeriesAt
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {R : ℝ}
    (hR : 0 < R)
    (hp : HasFPowerSeriesAt f p 0)
    (hd : DifferentiableOn ℂ f (Metric.closedBall 0 R)) (n : ℕ) :
    p.coeff n =
      (2 * Real.pi * I : ℂ)⁻¹ •
        circleIntegral
          (fun z => ((1 : ℂ) / (z - 0)) ^ n • (z - 0)⁻¹ • f z)
          0 R := by
  have hq : HasFPowerSeriesAt f (cauchyPowerSeries f 0 R) 0 := by
    have hnn : 0 < ((⟨R, hR.le⟩ : ℝ≥0)) := by
      exact_mod_cast hR
    exact (hd.hasFPowerSeriesOnBall hnn).hasFPowerSeriesAt
  have hpq : p = cauchyPowerSeries f 0 R := hp.eq_formalMultilinearSeries hq
  calc
    p.coeff n = (cauchyPowerSeries f 0 R).coeff n := by rw [hpq]
    _ = (cauchyPowerSeries f 0 R n fun _ => (1 : ℂ)) := by rfl
    _ = _ := by exact cauchyPowerSeries_apply f 0 R n 1

end

open scoped BigOperators PowerSeries
open List Finset

noncomputable section

namespace FormalMultilinearSeries

lemma ofScalars_comp_coeff (a b : ℕ → ℂ) (n : ℕ) :
    ((FormalMultilinearSeries.ofScalars ℂ a).comp
      (FormalMultilinearSeries.ofScalars ℂ b)).coeff n =
      ∑ c : Composition n, a c.length * ∏ i : Fin c.length, b (c.blocksFun i) := by
  rw [FormalMultilinearSeries.coeff]
  simp [FormalMultilinearSeries.comp, FormalMultilinearSeries.applyComposition,
    FormalMultilinearSeries.ofScalars, ContinuousMultilinearMap.mkPiAlgebraFin_apply,
    List.prod_ofFn, smul_eq_mul]

end FormalMultilinearSeries

private lemma prod_coeff_eq_zero_of_not_pos {g : ℂ⟦X⟧}
    (hg : PowerSeries.constantCoeff g = 0)
    {d n : ℕ} (l : { l : Fin d → ℕ // ∑ i, l i = n })
    (hl : ¬ ∀ i, 0 < l.1 i) :
    (∏ i : Fin d, PowerSeries.coeff (l.1 i) g) = 0 := by
  classical
  push Not at hl
  rcases hl with ⟨i, hi⟩
  have hzero : l.1 i = 0 := Nat.eq_zero_of_le_zero hi
  rw [Finset.prod_eq_zero_iff]
  refine ⟨i, Finset.mem_univ _, ?_⟩
  rw [hzero]
  simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hg

private lemma coeff_pow_eq_zero_of_constantCoeff_eq_zero
    {g : ℂ⟦X⟧} (hg : PowerSeries.constantCoeff g = 0)
    {n d : ℕ} (hnd : n < d) :
    PowerSeries.coeff n (g ^ d) = 0 := by
  set_option backward.isDefEq.respectTransparency false in
    exact PowerSeries.coeff_of_lt_order n
      (lt_of_lt_of_le (by exact_mod_cast hnd)
        (PowerSeries.le_order_pow_of_constantCoeff_eq_zero d hg))

private lemma coeff_pow_eq_sum_composition_length {g : ℂ⟦X⟧}
    (hg : PowerSeries.constantCoeff g = 0) (d n : ℕ) :
    PowerSeries.coeff n (g ^ d) =
      ∑ c : { c : Composition n // c.length = d },
        ∏ i : Fin c.1.length, PowerSeries.coeff (c.1.blocksFun i) g := by
  classical
  rw [PowerSeries.coeff_pow]
  let A := (Finset.range d).finsuppAntidiag n
  let B := { l : Fin d → ℕ // ∑ i, l i = n }
  letI : Fintype B := Fintype.ofEquiv A (finsuppAntidiagRangeEquivFin n d)
  let P : B → Prop := fun l => ∀ i, 0 < l.1 i
  let Pos := { l : Fin d → ℕ // (∀ i, 0 < l i) ∧ ∑ i, l i = n }
  letI : Fintype Pos := Fintype.ofEquiv { x : B // P x } (positiveSubtypeEquiv n d)
  have h_antidiag_to_B :
      (∑ l ∈ (Finset.range d).finsuppAntidiag n,
          ∏ i ∈ Finset.range d, PowerSeries.coeff (l i) g) =
        ∑ l : B, ∏ i : Fin d, PowerSeries.coeff (l.1 i) g := by
    calc
      (∑ l ∈ (Finset.range d).finsuppAntidiag n,
          ∏ i ∈ Finset.range d, PowerSeries.coeff (l i) g) =
          ∑ a : A, ∏ i ∈ Finset.range d, PowerSeries.coeff (a.1 i) g := by
        simpa [A] using (Finset.sum_attach A
          (fun a : ℕ →₀ ℕ => ∏ i ∈ Finset.range d, PowerSeries.coeff (a i) g)).symm
      _ = ∑ l : B, ∏ i : Fin d, PowerSeries.coeff (l.1 i) g := by
        exact Fintype.sum_equiv (finsuppAntidiagRangeEquivFin n d)
          (fun a : A => ∏ i ∈ Finset.range d, PowerSeries.coeff (a.1 i) g)
          (fun l : B => ∏ i : Fin d, PowerSeries.coeff (l.1 i) g)
          (by
            intro a
            calc
              (∏ i ∈ Finset.range d, PowerSeries.coeff (a.1 i) g) =
                  ∏ i : Fin d, PowerSeries.coeff (a.1 i.val) g := by
                exact (Fin.prod_univ_eq_prod_range
                  (fun i => PowerSeries.coeff (a.1 i) g) d).symm
              _ = ∏ i : Fin d,
                    PowerSeries.coeff (((finsuppAntidiagRangeEquivFin n d) a).1 i) g := by
                simp [finsuppAntidiagRangeEquivFin])
  rw [h_antidiag_to_B]
  have h_filter :
      (∑ l : B, ∏ i : Fin d, PowerSeries.coeff (l.1 i) g) =
        ∑ l : { x : B // P x },
          ∏ i : Fin d, PowerSeries.coeff (l.1.1 i) g := by
    have hsubset : (Finset.univ.filter P) ⊆ (Finset.univ : Finset B) := by
      intro x _hx
      simp
    have hsum_subset :
        ∑ x ∈ (Finset.univ.filter P), (∏ i : Fin d, PowerSeries.coeff (x.1 i) g) =
          ∑ x : B, ∏ i : Fin d, PowerSeries.coeff (x.1 i) g := by
      refine Finset.sum_subset hsubset ?_
      intro x _hx hxnot
      exact prod_coeff_eq_zero_of_not_pos hg x (by simpa [P] using hxnot)
    calc
      (∑ l : B, ∏ i : Fin d, PowerSeries.coeff (l.1 i) g) =
          ∑ x ∈ (Finset.univ.filter P), (∏ i : Fin d, PowerSeries.coeff (x.1 i) g) :=
        hsum_subset.symm
      _ = ∑ l : { x : B // P x },
          ∏ i : Fin d, PowerSeries.coeff (l.1.1 i) g := by
        refine Finset.sum_subtype (Finset.univ.filter P) ?_
          (fun x : B => ∏ i : Fin d, PowerSeries.coeff (x.1 i) g)
        intro x
        simp [P]
  rw [h_filter]
  calc
    (∑ l : { x : B // P x },
        ∏ i : Fin d, PowerSeries.coeff (l.1.1 i) g) =
      ∑ l : Pos,
        ∏ i : Fin d, PowerSeries.coeff (l.1 i) g := by
      exact Fintype.sum_equiv (positiveSubtypeEquiv n d)
        (fun l : { x : B // P x } =>
          ∏ i : Fin d, PowerSeries.coeff (l.1.1 i) g)
        (fun l : Pos =>
          ∏ i : Fin d, PowerSeries.coeff (l.1 i) g)
        (by intro l; rfl)
    _ = ∑ c : { c : Composition n // c.length = d },
        ∏ i : Fin c.1.length, PowerSeries.coeff (c.1.blocksFun i) g := by
      exact Fintype.sum_equiv (positiveFinTupleCompositionEquiv n d)
        (fun l : Pos =>
          ∏ i : Fin d, PowerSeries.coeff (l.1 i) g)
        (fun c : { c : Composition n // c.length = d } =>
          ∏ i : Fin c.1.length, PowerSeries.coeff (c.1.blocksFun i) g)
        (by
          intro l
          change (∏ i : Fin d, PowerSeries.coeff (l.1 i) g) =
            ∏ i : Fin (List.ofFn l.1).length,
              PowerSeries.coeff ((List.ofFn l.1).get i) g
          exact Fintype.prod_equiv (finCongr (by simp [List.length_ofFn]))
            (fun i : Fin d => PowerSeries.coeff (l.1 i) g)
            (fun i : Fin (List.ofFn l.1).length =>
              PowerSeries.coeff ((List.ofFn l.1).get i) g)
            (by intro i; simp))

private lemma subst_coeff_eq_sum_composition {f g : ℂ⟦X⟧}
    (hg : PowerSeries.constantCoeff g = 0) (n : ℕ) :
    PowerSeries.coeff n (f.subst g) =
      ∑ c : Composition n,
        PowerSeries.coeff c.length f *
          ∏ i : Fin c.length, PowerSeries.coeff (c.blocksFun i) g := by
  classical
  have hsubst := PowerSeries.coeff_subst'
    (PowerSeries.HasSubst.of_constantCoeff_zero' hg) f n
  rw [hsubst]
  simp only [smul_eq_mul]
  let term : ℕ → ℂ := fun d => PowerSeries.coeff d f * PowerSeries.coeff n (g ^ d)
  have hsupport : Function.support term ⊆ (Finset.range (n + 1) : Set ℕ) := by
    intro d hd
    rw [Finset.mem_coe, Finset.mem_range]
    by_contra hmem
    have hnd : n < d := by omega
    have hz : PowerSeries.coeff n (g ^ d) = 0 :=
      coeff_pow_eq_zero_of_constantCoeff_eq_zero hg hnd
    have hdne : term d ≠ 0 := hd
    simp [term, hz] at hdne
  calc
    (∑ᶠ d : ℕ, PowerSeries.coeff d f * PowerSeries.coeff n (g ^ d)) =
        ∑ d ∈ Finset.range (n + 1), PowerSeries.coeff d f * PowerSeries.coeff n (g ^ d) := by
      simpa [term] using finsum_eq_sum_of_support_subset term hsupport
    _ = ∑ d ∈ Finset.range (n + 1),
        ∑ c : { c : Composition n // c.length = d },
          PowerSeries.coeff d f *
            ∏ i : Fin c.1.length, PowerSeries.coeff (c.1.blocksFun i) g := by
      refine Finset.sum_congr rfl ?_
      intro d _hd
      rw [coeff_pow_eq_sum_composition_length hg d n]
      simp [Finset.mul_sum]
    _ = ∑ c : Composition n,
        PowerSeries.coeff c.length f *
          ∏ i : Fin c.length, PowerSeries.coeff (c.blocksFun i) g := by
      rw [← Fin.sum_univ_eq_sum_range
        (fun d => ∑ c : { c : Composition n // c.length = d },
          PowerSeries.coeff d f *
            ∏ i : Fin c.1.length, PowerSeries.coeff (c.1.blocksFun i) g) (n + 1)]
      rw [← Fintype.sum_sigma (fun x : Sigma (fun d : Fin (n + 1) =>
          { c : Composition n // c.length = d.val }) =>
        PowerSeries.coeff x.1.val f *
          ∏ i : Fin x.2.1.length, PowerSeries.coeff (x.2.1.blocksFun i) g)]
      exact Fintype.sum_equiv (sigmaLengthCompositionEquiv n)
        (fun x : Sigma (fun d : Fin (n + 1) =>
          { c : Composition n // c.length = d.val }) =>
          PowerSeries.coeff x.1.val f *
            ∏ i : Fin x.2.1.length, PowerSeries.coeff (x.2.1.blocksFun i) g)
        (fun c : Composition n =>
          PowerSeries.coeff c.length f *
            ∏ i : Fin c.length, PowerSeries.coeff (c.blocksFun i) g)
        (by
          intro x
          rcases x with ⟨d, c, hc⟩
          dsimp [sigmaLengthCompositionEquiv]
          apply congrArg₂ HMul.hMul
          · exact congrArg (fun k => PowerSeries.coeff k f) hc.symm
          · rfl)

namespace PowerSeries

theorem toFMLS_subst_eq_comp {f g : PowerSeries ℂ}
    (hg : PowerSeries.constantCoeff g = 0) :
    PowerSeries.toFMLS (f.subst g) =
      (PowerSeries.toFMLS f).comp (PowerSeries.toFMLS g) := by
  ext n
  simp [PowerSeries.coeff_toFMLS]
  change PowerSeries.coeff n (f.subst g) =
    ((FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff n f)).comp
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff n g))).coeff n
  rw [FormalMultilinearSeries.ofScalars_comp_coeff]
  exact subst_coeff_eq_sum_composition hg n

end PowerSeries
end

/-!
# Saddle-point assembly bricks

This file contains the exact Cauchy parameterization on `[-pi, pi]` and the
bounded algebraic assembly theorem for a central/tail saddle decomposition.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal

noncomputable section

private lemma saddlePhase_periodic (n : ℕ) :
    Function.Periodic (fun θ : ℝ => Complex.exp (-(↑↑n * ↑θ) * Complex.I))
      (2 * Real.pi) := by
  intro θ
  change Complex.exp (-(↑↑n * ↑(θ + 2 * Real.pi)) * Complex.I) =
    Complex.exp (-(↑↑n * ↑θ) * Complex.I)
  rw [show -(↑↑n * ↑(θ + 2 * Real.pi)) * I =
      -(↑↑n * ↑θ) * I - ↑n * (2 * ↑Real.pi * I) by
    simp only [Complex.ofReal_add, Complex.ofReal_mul]
    norm_num
    ring_nf]
  exact Complex.exp_periodic.sub_nat_mul_eq n

private lemma saddleRawIntegrand_periodic (f : ℂ → ℂ) (r : ℝ) (n : ℕ) :
    Function.Periodic (saddleRawIntegrand f r n) (2 * Real.pi) := by
  have hcircle0 :
      Function.Periodic (fun θ : ℝ => f (circleMap (0 : ℂ) r θ)) (2 * Real.pi) :=
    (periodic_circleMap (0 : ℂ) r).comp f
  have hcircle :
      Function.Periodic
        (fun θ : ℝ => f ((r : ℂ) * Complex.exp (θ * Complex.I))) (2 * Real.pi) := by
    simpa [circleMap_zero] using hcircle0
  exact hcircle.mul (saddlePhase_periodic n)

private lemma saddleRawIntegral_zero_to_neg_pi (f : ℂ → ℂ) (r : ℝ) (n : ℕ) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, saddleRawIntegrand f r n θ) =
      ∫ θ in (-Real.pi)..Real.pi, saddleRawIntegrand f r n θ := by
  have h := (saddleRawIntegrand_periodic f r n).intervalIntegral_add_eq (-Real.pi) 0
  simpa [two_mul, add_comm, add_left_comm, add_assoc] using h.symm

private lemma cauchyCircleIntegrand_param_eq
    (f : ℂ → ℂ) {r : ℝ} (hr : 0 < r) (n : ℕ) (θ : ℝ) :
    deriv (circleMap (0 : ℂ) r) θ •
      (((1 : ℂ) / (circleMap (0 : ℂ) r θ - 0)) ^ n •
        (circleMap (0 : ℂ) r θ - 0)⁻¹ • f (circleMap (0 : ℂ) r θ)) =
    Complex.I * ((r : ℂ)⁻¹ ^ n) * saddleRawIntegrand f r n θ := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hcircle : deriv (circleMap (0 : ℂ) r) θ =
      circleMap (0 : ℂ) r θ * Complex.I :=
    _root_.deriv_circleMap (0 : ℂ) r θ
  rw [hcircle]
  simp [saddleRawIntegrand, circleMap_zero, smul_eq_mul, div_eq_mul_inv,
    mul_pow, Complex.exp_neg, mul_comm, mul_left_comm, mul_assoc]
  field_simp [hrC, Complex.exp_ne_zero]
  rw [← Complex.exp_nat_mul]
  ring_nf

private lemma two_pi_I_inv_mul_I :
    ((2 * Real.pi * Complex.I : ℂ)⁻¹ * Complex.I) = (2 * Real.pi : ℂ)⁻¹ := by
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have htwo : (2 * Real.pi : ℂ) ≠ 0 := by
    norm_num [Real.pi_ne_zero]
  field_simp [hI, htwo]

/-- Cauchy's coefficient formula parameterized on the interval `[-pi, pi]`. -/
theorem coeff_eq_saddle_param
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {r : ℝ}
    (hr : 0 < r)
    (hp : HasFPowerSeriesAt f p 0)
    (hd : DifferentiableOn ℂ f (Metric.closedBall 0 r)) (n : ℕ) :
    p.coeff n =
      (2 * Real.pi : ℂ)⁻¹ * (r : ℂ)⁻¹ ^ n *
        ∫ θ in (-Real.pi)..Real.pi, saddleRawIntegrand f r n θ := by
  set_option backward.isDefEq.respectTransparency false in
    have hc := coeff_eq_cauchy_circleIntegral_of_hasFPowerSeriesAt hr hp hd n
    rw [hc]
    rw [circleIntegral]
    have hcongr :
        (∫ θ in (0 : ℝ)..2 * Real.pi,
            deriv (circleMap (0 : ℂ) r) θ •
              (((1 : ℂ) / (circleMap (0 : ℂ) r θ - 0)) ^ n •
                (circleMap (0 : ℂ) r θ - 0)⁻¹ • f (circleMap (0 : ℂ) r θ))) =
          ∫ θ in (0 : ℝ)..2 * Real.pi,
            Complex.I * ((r : ℂ)⁻¹ ^ n) * saddleRawIntegrand f r n θ := by
      apply intervalIntegral.integral_congr
      intro θ _
      exact cauchyCircleIntegrand_param_eq f hr n θ
    rw [hcongr]
    rw [show (∫ θ in (0 : ℝ)..2 * Real.pi,
            Complex.I * ((r : ℂ)⁻¹ ^ n) * saddleRawIntegrand f r n θ) =
          Complex.I * ((r : ℂ)⁻¹ ^ n) *
            ∫ θ in (0 : ℝ)..2 * Real.pi, saddleRawIntegrand f r n θ by
      calc
        (∫ θ in (0 : ℝ)..2 * Real.pi,
            Complex.I * ((r : ℂ)⁻¹ ^ n) * saddleRawIntegrand f r n θ)
            = ∫ θ in (0 : ℝ)..2 * Real.pi,
                Complex.I * (((r : ℂ)⁻¹ ^ n) * saddleRawIntegrand f r n θ) := by
              apply intervalIntegral.integral_congr
              intro θ _
              ring
        _ = Complex.I *
              (∫ θ in (0 : ℝ)..2 * Real.pi,
                ((r : ℂ)⁻¹ ^ n) * saddleRawIntegrand f r n θ) := by
              exact intervalIntegral.integral_const_mul (a := (0 : ℝ)) (b := 2 * Real.pi)
                (μ := MeasureTheory.volume) (r := Complex.I)
                (f := fun θ => ((r : ℂ)⁻¹ ^ n) * saddleRawIntegrand f r n θ)
        _ = Complex.I * (((r : ℂ)⁻¹ ^ n) *
              ∫ θ in (0 : ℝ)..2 * Real.pi, saddleRawIntegrand f r n θ) := by
              exact congrArg (fun z : ℂ => Complex.I * z)
                (intervalIntegral.integral_const_mul (a := (0 : ℝ)) (b := 2 * Real.pi)
                  (μ := MeasureTheory.volume) (r := ((r : ℂ)⁻¹ ^ n))
                  (f := fun θ => saddleRawIntegrand f r n θ))
        _ = Complex.I * ((r : ℂ)⁻¹ ^ n) *
              ∫ θ in (0 : ℝ)..2 * Real.pi, saddleRawIntegrand f r n θ := by
              ring]
    rw [saddleRawIntegral_zero_to_neg_pi]
    calc
      (2 * Real.pi * Complex.I : ℂ)⁻¹ •
          (Complex.I * ((r : ℂ)⁻¹ ^ n) *
            ∫ θ in (-Real.pi)..Real.pi, saddleRawIntegrand f r n θ)
          =
            ((((2 * Real.pi : ℂ) * Complex.I)⁻¹) * Complex.I) *
              ((r : ℂ)⁻¹ ^ n) *
                ∫ θ in (-Real.pi)..Real.pi, saddleRawIntegrand f r n θ := by
              simp [smul_eq_mul]
              ring
      _ = (2 * Real.pi : ℂ)⁻¹ * (r : ℂ)⁻¹ ^ n *
            ∫ θ in (-Real.pi)..Real.pi, saddleRawIntegrand f r n θ := by
              rw [two_pi_I_inv_mul_I]

private lemma saddleRawIntegrand_eq_const_mul_saddleGAt
    (f : ℂ → ℂ) {r : ℝ} (hfnz : f (r : ℂ) ≠ 0) (n : ℕ) (θ : ℝ) :
    saddleRawIntegrand f r n θ = f (r : ℂ) * saddleGAt f r n θ := by
  simp [saddleRawIntegrand, saddleGAt, div_eq_mul_inv, mul_comm, mul_assoc]
  field_simp [hfnz]

/-- Cauchy's parameterization in normalized saddle-integral form. -/
theorem coeff_eq_saddle_param_normalized
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {r : ℝ}
    (hr : 0 < r)
    (hp : HasFPowerSeriesAt f p 0)
    (hd : DifferentiableOn ℂ f (Metric.closedBall 0 r))
    (hfnz : f (r : ℂ) ≠ 0) (n : ℕ) :
    p.coeff n = saddlePrefAt f r n * saddleJfullAt f r n := by
  rw [coeff_eq_saddle_param hr hp hd n]
  have hraw :
      (∫ θ in (-Real.pi)..Real.pi, saddleRawIntegrand f r n θ) =
        f (r : ℂ) * ∫ θ in (-Real.pi)..Real.pi, saddleGAt f r n θ := by
    calc
      (∫ θ in (-Real.pi)..Real.pi, saddleRawIntegrand f r n θ)
          = ∫ θ in (-Real.pi)..Real.pi, f (r : ℂ) * saddleGAt f r n θ := by
            apply intervalIntegral.integral_congr
            intro θ _
            exact saddleRawIntegrand_eq_const_mul_saddleGAt f hfnz n θ
      _ = f (r : ℂ) * ∫ θ in (-Real.pi)..Real.pi, saddleGAt f r n θ := by
            exact intervalIntegral.integral_const_mul (a := -Real.pi) (b := Real.pi)
              (μ := MeasureTheory.volume) (r := f (r : ℂ)) (f := fun θ => saddleGAt f r n θ)
  rw [hraw]
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  simp [saddlePrefAt, saddleJfullAt]
  field_simp [hrC]

/-- Split the full normalized integral into central and tail pieces. -/
theorem saddleJfullAt_eq_saddleJcAt_add_saddleJtAt
    (f : ℂ → ℂ) (r δ : ℝ) (n : ℕ)
    (hleft : IntervalIntegrable (saddleGAt f r n) MeasureTheory.volume (-Real.pi) (-δ))
    (hcenter : IntervalIntegrable (saddleGAt f r n) MeasureTheory.volume (-δ) δ)
    (hright : IntervalIntegrable (saddleGAt f r n) MeasureTheory.volume δ Real.pi) :
    saddleJfullAt f r n = saddleJcAt f r δ n + saddleJtAt f r δ n := by
  have h12 := intervalIntegral.integral_add_adjacent_intervals hleft hcenter
  have hfull := intervalIntegral.integral_add_adjacent_intervals (hleft.trans hcenter) hright
  unfold saddleJfullAt saddleJcAt saddleJtAt
  rw [← hfull, ← h12]
  ring

/-- Exact coefficient split into the central window and the two tails. -/
theorem coeff_eq_saddle_split
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} {r δ : ℝ} {n : ℕ}
    (hr : 0 < r)
    (hp : HasFPowerSeriesAt f p 0)
    (hd : DifferentiableOn ℂ f (Metric.closedBall 0 r))
    (hfnz : f (r : ℂ) ≠ 0)
    (hleft : IntervalIntegrable (saddleGAt f r n) MeasureTheory.volume (-Real.pi) (-δ))
    (hcenter : IntervalIntegrable (saddleGAt f r n) MeasureTheory.volume (-δ) δ)
    (hright : IntervalIntegrable (saddleGAt f r n) MeasureTheory.volume δ Real.pi) :
    p.coeff n = saddlePrefAt f r n * (saddleJcAt f r δ n + saddleJtAt f r δ n) := by
  rw [coeff_eq_saddle_param_normalized hr hp hd hfnz n]
  rw [saddleJfullAt_eq_saddleJcAt_add_saddleJtAt f r δ n hleft hcenter hright]

/-- Eventual sequence version of the exact central/tail split. -/
theorem eventually_coeff_eq_saddle_split
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} (r δ : ℕ → ℝ)
    (hp : HasFPowerSeriesAt f p 0)
    (hr : ∀ᶠ n in atTop, 0 < r n)
    (hd : ∀ᶠ n in atTop, DifferentiableOn ℂ f (Metric.closedBall 0 (r n)))
    (hfnz : ∀ᶠ n in atTop, f (r n : ℂ) ≠ 0)
    (hleft : ∀ᶠ n in atTop,
      IntervalIntegrable (saddleG f r n) MeasureTheory.volume (-Real.pi) (-(δ n)))
    (hcenter : ∀ᶠ n in atTop,
      IntervalIntegrable (saddleG f r n) MeasureTheory.volume (-(δ n)) (δ n))
    (hright : ∀ᶠ n in atTop,
      IntervalIntegrable (saddleG f r n) MeasureTheory.volume (δ n) Real.pi) :
    ∀ᶠ n in atTop,
      p.coeff n = saddlePref f r n * (saddleJc f r δ n + saddleJt f r δ n) := by
  filter_upwards [hr, hd, hfnz, hleft, hcenter, hright] with
    n hrn hdn hfnzn hleftn hcentern hrightn
  simpa [saddlePref, saddleJc, saddleJt, saddleG] using
    coeff_eq_saddle_split (f := f) (p := p) (r := r n) (δ := δ n) (n := n)
      hrn hp hdn hfnzn hleftn hcentern hrightn

end

open Complex
open scoped NNReal ENNReal

noncomputable section

theorem expCarrier_toFMLS_eq_expSeries :
    PowerSeries.toFMLS expCarrier = NormedSpace.expSeries ℂ ℂ := by
  rw [NormedSpace.expSeries_eq_ofScalars]
  ext n
  simp [PowerSeries.toFMLS, expCarrier]

end

open Complex
open scoped NNReal ENNReal

noncomputable section

theorem bellCarrier_eq_complex_subst :
    bellCarrier = (PowerSeries.exp ℂ).subst (PowerSeries.exp ℂ - 1) := by
  set_option backward.isDefEq.respectTransparency false in
    rw [bellCarrier, AnalyticCombinatorics.Ch1.CombClass.egf_bell]
    have hsubst : PowerSeries.HasSubst (PowerSeries.exp ℚ - 1 : PowerSeries ℚ) := by
      apply PowerSeries.HasSubst.of_constantCoeff_zero'
      simp
    change (PowerSeries.map (algebraMap ℚ ℂ)
        ((PowerSeries.exp ℚ).subst (PowerSeries.exp ℚ - 1))) = _
    simpa using
      (PowerSeries.map_subst (a := (PowerSeries.exp ℚ - 1 : PowerSeries ℚ))
        (h := algebraMap ℚ ℂ) hsubst (PowerSeries.exp ℚ))

end

open scoped PowerSeries

noncomputable section

theorem bellCarrier_toFMLS_eq_analyticBellSeries :
    PowerSeries.toFMLS bellCarrier = analyticBellSeries := by
  rw [bellCarrier_eq_complex_subst]
  rw [PowerSeries.toFMLS_subst_eq_comp]
  · change (PowerSeries.toFMLS expCarrier).comp
        (PowerSeries.toFMLS (PowerSeries.exp ℂ - 1)) =
      analyticBellSeries
    rw [expCarrier_toFMLS_eq_expSeries]
    have hinner : PowerSeries.toFMLS (PowerSeries.exp ℂ - 1) =
        expSeriesC - constFormalMultilinearSeries ℂ ℂ (1 : ℂ) := by
      ext n
      cases n <;>
        simp [PowerSeries.toFMLS, expSeriesC, NormedSpace.expSeries_eq_ofScalars,
          constFormalMultilinearSeries]
    rw [hinner]
  · simp

end

/-!
# Gaussian central saddle core

This file packages the reusable dominated-convergence core for the central
Gaussian window after the saddle scaling `theta = x / sqrt (B n)`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval

noncomputable section

/-- The normalized Gaussian integral used by the saddle central window. -/
theorem gaussian_integral_half :
    (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2)) =
      (Real.sqrt (2 * Real.pi) : ℂ) := by
  set_option backward.isDefEq.respectTransparency false in
    have hgauss :=
      integral_gaussian_complex (b := (1 / 2 : ℂ))
        (by norm_num : 0 < (Complex.re (1 / 2 : ℂ)))
    rw [show (fun x : ℝ => Complex.exp (-(x ^ 2) / 2)) =
        (fun x : ℝ => Complex.exp (-(1 / 2 : ℂ) * (x : ℂ) ^ 2)) by
          funext x
          norm_num
          ring_nf]
    rw [hgauss]
    have hbase : (↑Real.pi / (1 / 2 : ℂ)) = (↑(2 * Real.pi) : ℂ) := by
      norm_num [div_eq_mul_inv]
      ring
    rw [hbase]
    have hexp : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
    rw [hexp]
    rw [← Complex.ofReal_cpow]
    · rw [Complex.ofReal_inj]
      rw [Real.sqrt_eq_rpow]
    · positivity

private lemma saddle_scaled_constant (B : ℕ → ℝ) (n : ℕ) (hB : 0 < B n) :
    (Real.sqrt (2 * Real.pi * B n) : ℂ) * (2 * Real.pi : ℂ)⁻¹ *
      ((Real.sqrt (B n))⁻¹ : ℂ) =
      (1 / Real.sqrt (2 * Real.pi) : ℂ) := by
  let c : ℝ := Real.sqrt (B n)
  have hc_pos : 0 < c := by simpa [c] using Real.sqrt_pos.mpr hB
  have hc_ne : c ≠ 0 := hc_pos.ne'
  have hsqrt2_pos : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hsqrt2_ne : Real.sqrt (2 * Real.pi) ≠ 0 := hsqrt2_pos.ne'
  have hsqrt_prod :
      Real.sqrt (2 * Real.pi * B n) = Real.sqrt (2 * Real.pi) * c := by
    rw [show 2 * Real.pi * B n = (2 * Real.pi) * B n by ring]
    rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi)]
  have hconstR :
      Real.sqrt (2 * Real.pi * B n) * (2 * Real.pi)⁻¹ * c⁻¹ =
        1 / Real.sqrt (2 * Real.pi) := by
    rw [hsqrt_prod]
    calc
      (Real.sqrt (2 * Real.pi) * c) * (2 * Real.pi)⁻¹ * c⁻¹
          = Real.sqrt (2 * Real.pi) * (2 * Real.pi)⁻¹ := by
            field_simp [hc_ne]
      _ = Real.sqrt (2 * Real.pi) / (2 * Real.pi) := by
            rw [div_eq_mul_inv]
      _ = Real.sqrt (2 * Real.pi) /
            (Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi)) := by
            congr 1
            rw [← sq]
            rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)]
      _ = 1 / Real.sqrt (2 * Real.pi) := by
            field_simp [hsqrt2_ne]
  norm_cast

/--
After the scaling `theta = x / sqrt (B n)`, the central saddle integral has
the normalized full Gaussian prefactor.
-/
theorem saddleJc_eq_integral_scaled
    (f : ℂ → ℂ) (r δ B : ℕ → ℝ) (n : ℕ) (hB : 0 < B n) :
    (Real.sqrt (2 * Real.pi * B n) : ℂ) * saddleJc f r δ n =
      (1 / Real.sqrt (2 * Real.pi) : ℂ) *
        ∫ x in -(δ n * Real.sqrt (B n))..(δ n * Real.sqrt (B n)),
          saddleG f r n (x / Real.sqrt (B n)) := by
  let c : ℝ := Real.sqrt (B n)
  have hc_pos : 0 < c := by simpa [c] using Real.sqrt_pos.mpr hB
  have hc_ne : c ≠ 0 := hc_pos.ne'
  have hsubst :
      (∫ θ in (-(δ n))..(δ n), saddleG f r n θ) =
        c⁻¹ • ∫ x in -(δ n * c)..(δ n * c), saddleG f r n (x / c) := by
    have h := intervalIntegral.inv_smul_integral_comp_div
      (f := fun θ : ℝ => saddleG f r n θ)
      (a := -(δ n * c)) (b := δ n * c) c
    have hb : δ n * c / c = δ n := by
      exact mul_div_cancel_right₀ (δ n) hc_ne
    have ha : -(δ n * c) / c = -(δ n) := by
      rw [neg_div, hb]
    rw [ha, hb] at h
    exact h.symm
  unfold saddleJc saddleJcAt
  change (Real.sqrt (2 * Real.pi * B n) : ℂ) *
      ((2 * Real.pi : ℂ)⁻¹ * ∫ θ in (-(δ n))..(δ n), saddleG f r n θ) =
    (1 / Real.sqrt (2 * Real.pi) : ℂ) *
      ∫ x in -(δ n * c)..(δ n * c), saddleG f r n (x / c)
  rw [hsubst]
  rw [show ((c⁻¹ : ℝ) •
        ∫ (x : ℝ) in -(δ n * c)..δ n * c, saddleG f r n (x / c)) =
      ((c⁻¹ : ℂ) *
        ∫ (x : ℝ) in -(δ n * c)..δ n * c, saddleG f r n (x / c)) by
        simp]
  rw [← mul_assoc]
  rw [← mul_assoc]
  rw [show (Real.sqrt (2 * Real.pi * B n) : ℂ) * (2 * Real.pi : ℂ)⁻¹ *
      (c⁻¹ : ℂ) = (1 / Real.sqrt (2 * Real.pi) : ℂ) by
        simpa [c] using saddle_scaled_constant B n hB]

end

/-!
# H-admissible saddle-point bridge

This file packages the abstract H-admissible hypotheses needed to feed the
central Gaussian core, the tail estimate, and the Cauchy assembly theorem.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval

noncomputable section

lemma saddleGAt_eq_gaussian_mul_saddleLocalRatio
    (f : ℂ → ℂ) (a b : ℝ → ℝ) (r x : ℝ) (n : ℕ)
    (hb : 0 < b r) (ha : a r = (n : ℝ)) :
    saddleGAt f r n (x / Real.sqrt (b r)) =
      Complex.exp (-(x ^ 2) / 2) *
        saddleLocalRatio f a b r (x / Real.sqrt (b r)) := by
  let θ : ℝ := x / Real.sqrt (b r)
  have hsqrt_pos : 0 < Real.sqrt (b r) := Real.sqrt_pos.mpr hb
  have hsqrt_ne : Real.sqrt (b r) ≠ 0 := hsqrt_pos.ne'
  have hquad : b r * θ ^ 2 / 2 = x ^ 2 / 2 := by
    dsimp [θ]
    rw [div_pow]
    field_simp [hsqrt_ne]
    rw [Real.sq_sqrt hb.le]
    ring
  have hphaseR : (n : ℝ) * θ = a r * θ := by
    rw [ha]
  have hphaseC :
      Complex.exp (-(↑↑n * ↑θ) * I) =
        Complex.exp (-(a r * θ : ℝ) * I) := by
    congr 1
    have hmulC : (n : ℂ) * (θ : ℂ) = ((a r * θ : ℝ) : ℂ) := by
      exact_mod_cast hphaseR
    rw [hmulC]
  have hden :
      Complex.exp (-(b r * θ ^ 2 / 2 : ℝ)) =
        Complex.exp ((-(x ^ 2) / 2 : ℝ) : ℂ) := by
    congr 1
    exact_mod_cast (by linarith [hquad] :
      -(b r * θ ^ 2 / 2) = -(x ^ 2) / 2)
  have hgauss :
      Complex.exp (-(x ^ 2) / 2) =
        Complex.exp ((-(x ^ 2) / 2 : ℝ) : ℂ) := by
    congr 1
    norm_num
  dsimp [θ] at hphaseC hden ⊢
  rw [hgauss]
  unfold saddleGAt saddleLocalRatio
  rw [hphaseC, hden]
  field_simp [Complex.exp_ne_zero ((-(x ^ 2) / 2 : ℝ) : ℂ)]

lemma saddleGAt_continuous_of_differentiableOn_closedBall
    (f : ℂ → ℂ) (r : ℝ) (n : ℕ) (hr : 0 ≤ r)
    (hf : DifferentiableOn ℂ f (Metric.closedBall (0 : ℂ) r)) :
    Continuous fun θ : ℝ => saddleGAt f r n θ := by
  have hfcirc0 : Continuous fun θ : ℝ => f (circleMap (0 : ℂ) r θ) :=
    hf.continuousOn.comp_continuous (continuous_circleMap (0 : ℂ) r)
      (fun θ => circleMap_mem_closedBall (0 : ℂ) hr θ)
  have hfcirc :
      Continuous fun θ : ℝ =>
        f ((r : ℂ) * Complex.exp (θ * Complex.I)) := by
    simpa [circleMap_zero] using hfcirc0
  have hphase :
      Continuous fun θ : ℝ => Complex.exp (-(↑↑n * ↑θ) * I) := by
    fun_prop
  simpa [saddleGAt, div_eq_mul_inv] using
    (hfcirc.mul continuous_const).mul hphase

lemma saddleGAt_intervalIntegrable_of_differentiableOn_closedBall
    (f : ℂ → ℂ) (r : ℝ) (n : ℕ) (a b : ℝ) (hr : 0 ≤ r)
    (hf : DifferentiableOn ℂ f (Metric.closedBall (0 : ℂ) r)) :
    IntervalIntegrable (saddleGAt f r n) volume a b :=
  (saddleGAt_continuous_of_differentiableOn_closedBall f r n hr hf).intervalIntegrable a b

lemma saddleJtAt_norm_le_of_tail_bound
    (f : ℂ → ℂ) (r δ E : ℝ) (n : ℕ)
    (hδ_nonneg : 0 ≤ δ) (hδπ : δ ≤ Real.pi) (hE_nonneg : 0 ≤ E)
    (htail : ∀ θ : ℝ, δ ≤ |θ| → |θ| ≤ Real.pi →
      ‖saddleGAt f r n θ‖ ≤ E) :
    ‖saddleJtAt f r δ n‖ ≤
      (‖((2 * Real.pi : ℂ)⁻¹)‖ * (2 * Real.pi)) * E := by
  have hleft :
      ‖∫ θ in (-Real.pi)..(-δ), saddleGAt f r n θ‖ ≤
        E * |(-δ) - (-Real.pi)| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro θ hθ
    have hθI : -Real.pi < θ ∧ θ ≤ -δ := by
      simpa [Set.uIoc_of_le (by linarith : -Real.pi ≤ -δ)] using hθ
    have hθ_nonpos : θ ≤ 0 := by linarith
    have hδθ : δ ≤ |θ| := by
      rw [abs_of_nonpos hθ_nonpos]
      linarith
    have hθπ : |θ| ≤ Real.pi := by
      rw [abs_of_nonpos hθ_nonpos]
      linarith
    exact htail θ hδθ hθπ
  have hright :
      ‖∫ θ in δ..Real.pi, saddleGAt f r n θ‖ ≤
        E * |Real.pi - δ| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro θ hθ
    have hθI : δ < θ ∧ θ ≤ Real.pi := by
      simpa [Set.uIoc_of_le hδπ] using hθ
    have hθ_nonneg : 0 ≤ θ := by linarith
    have hδθ : δ ≤ |θ| := by
      rw [abs_of_nonneg hθ_nonneg]
      linarith
    have hθπ : |θ| ≤ Real.pi := by
      rw [abs_of_nonneg hθ_nonneg]
      exact hθI.2
    exact htail θ hδθ hθπ
  have hlen_right : |Real.pi - δ| ≤ Real.pi := by
    rw [abs_of_nonneg (sub_nonneg.mpr hδπ)]
    linarith [Real.pi_pos]
  have hlen_left : |(-δ) - (-Real.pi)| ≤ Real.pi := by
    rw [show (-δ) - (-Real.pi) = Real.pi - δ by ring]
    exact hlen_right
  have hleft_pi :
      ‖∫ θ in (-Real.pi)..(-δ), saddleGAt f r n θ‖ ≤
        E * Real.pi :=
    hleft.trans (mul_le_mul_of_nonneg_left hlen_left hE_nonneg)
  have hright_pi :
      ‖∫ θ in δ..Real.pi, saddleGAt f r n θ‖ ≤
        E * Real.pi :=
    hright.trans (mul_le_mul_of_nonneg_left hlen_right hE_nonneg)
  unfold saddleJtAt
  calc
    ‖(2 * Real.pi : ℂ)⁻¹ *
        ((∫ θ in (-Real.pi)..(-δ), saddleGAt f r n θ) +
          ∫ θ in δ..Real.pi, saddleGAt f r n θ)‖
        ≤ ‖((2 * Real.pi : ℂ)⁻¹)‖ *
          (‖∫ θ in (-Real.pi)..(-δ), saddleGAt f r n θ‖ +
            ‖∫ θ in δ..Real.pi, saddleGAt f r n θ‖) := by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
    _ ≤ ‖((2 * Real.pi : ℂ)⁻¹)‖ * (E * Real.pi + E * Real.pi) := by
          exact mul_le_mul_of_nonneg_left (add_le_add hleft_pi hright_pi) (norm_nonneg _)
    _ = (‖((2 * Real.pi : ℂ)⁻¹)‖ * (2 * Real.pi)) * E := by
          ring

lemma f_ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) : z ≠ 0 := by
  intro hzero
  simp [hzero] at hz

lemma saddleScale_nonzero_of_pos
    (f : ℂ → ℂ) (r B : ℕ → ℝ) (n : ℕ)
    (hr : 0 < r n) (hf : 0 < (f (r n : ℂ)).re) (hB : 0 < B n) :
    saddleScale f r B n ≠ 0 := by
  have hfnz : f (r n : ℂ) ≠ 0 := f_ne_zero_of_re_pos hf
  have hrC : (r n : ℂ) ≠ 0 := by
    exact_mod_cast hr.ne'
  have hpow : (r n : ℂ) ^ n ≠ 0 := pow_ne_zero n hrC
  have hpref : saddlePref f r n ≠ 0 := by
    unfold saddlePref saddlePrefAt
    exact div_ne_zero hfnz hpow
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi * B n) := by
    exact Real.sqrt_pos.mpr (by positivity)
  have hsqrtC : (Real.sqrt (2 * Real.pi * B n) : ℂ) ≠ 0 := by
    exact_mod_cast hsqrt_pos.ne'
  unfold saddleScale
  exact div_ne_zero hpref hsqrtC

end

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-!
# Gaussian moments for the saddle correction

This file records the standard Gaussian moments needed by the second-order
saddle correction.
-/

open Complex Filter Asymptotics MeasureTheory ProbabilityTheory
open scoped Topology Real NNReal ENNReal Interval

noncomputable section

private lemma deriv_gaussianMGFCore :
    deriv gaussianMGFCore = fun t : ℝ => t * gaussianMGFCore t := by
  ext t
  unfold gaussianMGFCore
  rw [_root_.deriv_exp (by fun_prop)]
  simp only [deriv_div_const, differentiableAt_const, differentiableAt_fun_id, Nat.cast_ofNat,
    DifferentiableAt.fun_pow, deriv_fun_mul, deriv_const', zero_mul, deriv_fun_pow,
    Nat.add_one_sub_one, pow_one, deriv_id'', mul_one, zero_add]
  ring

private lemma deriv_t_mul_gaussianMGFCore :
    deriv (fun t : ℝ => t * gaussianMGFCore t) =
      fun t : ℝ => (1 + t ^ 2) * gaussianMGFCore t := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by unfold gaussianMGFCore; fun_prop)]
  rw [deriv_gaussianMGFCore]
  simp
  ring_nf

private lemma deriv_poly2_mul_gaussianMGFCore :
    deriv (fun t : ℝ => (1 + t ^ 2) * gaussianMGFCore t) =
      fun t : ℝ => (3 * t + t ^ 3) * gaussianMGFCore t := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by unfold gaussianMGFCore; fun_prop)]
  rw [deriv_gaussianMGFCore]
  simp only [differentiableAt_const, differentiableAt_fun_id, Nat.cast_ofNat,
    DifferentiableAt.fun_pow, DifferentiableAt.add, deriv_fun_add, deriv_const',
    deriv_fun_pow, Nat.add_one_sub_one, pow_one, deriv_id'', mul_one, zero_add]
  ring_nf

private lemma deriv_poly3_mul_gaussianMGFCore :
    deriv (fun t : ℝ => (3 * t + t ^ 3) * gaussianMGFCore t) =
      fun t : ℝ => (3 + 6 * t ^ 2 + t ^ 4) * gaussianMGFCore t := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by unfold gaussianMGFCore; fun_prop)]
  rw [deriv_gaussianMGFCore]
  simp only [differentiableAt_const, differentiableAt_fun_id, Nat.cast_ofNat,
    DifferentiableAt.fun_pow, DifferentiableAt.const_mul, DifferentiableAt.add,
    deriv_fun_add, deriv_const_mul, deriv_fun_pow, Nat.add_one_sub_one, pow_one,
    deriv_id'', mul_one]
  have hpoly : deriv (fun t : ℝ => 3 * t + t ^ 3) t = 3 + 3 * t ^ 2 := by
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    have hlin : deriv (fun y : ℝ => 3 * y) t = 3 := by
      rw [deriv_const_mul_field (u := (3 : ℝ)) (v := fun y : ℝ => y) (x := t)]
      simp [deriv_id'']
    have hpow : deriv (fun y : ℝ => y ^ 3) t = 3 * t ^ 2 := by
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    simpa [hlin, hpow]
  rw [hpoly]
  ring_nf

private lemma deriv_poly4_mul_gaussianMGFCore :
    deriv (fun t : ℝ => (3 + 6 * t ^ 2 + t ^ 4) * gaussianMGFCore t) =
      fun t : ℝ => (15 * t + 10 * t ^ 3 + t ^ 5) * gaussianMGFCore t := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by unfold gaussianMGFCore; fun_prop)]
  rw [deriv_gaussianMGFCore]
  simp only [differentiableAt_const, differentiableAt_fun_id, Nat.cast_ofNat,
    DifferentiableAt.fun_pow, DifferentiableAt.const_mul, DifferentiableAt.add,
    deriv_fun_add, deriv_const', deriv_const_mul, deriv_fun_pow, Nat.add_one_sub_one,
    pow_one, deriv_id'', mul_one, zero_add]
  have hpoly :
      deriv (fun t : ℝ => 3 + 6 * t ^ 2 + t ^ 4) t =
        12 * t + 4 * t ^ 3 := by
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    have hconst : deriv (fun _ : ℝ => (3 : ℝ)) t = 0 := by
      rw [deriv_const']
    have hquad : deriv (fun y : ℝ => 6 * y ^ 2) t = 12 * t := by
      rw [deriv_const_mul_field (u := (6 : ℝ)) (v := fun y : ℝ => y ^ 2) (x := t)]
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    have hquart : deriv (fun y : ℝ => y ^ 4) t = 4 * t ^ 3 := by
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    simpa [hconst, hquad, hquart]
  rw [hpoly]
  ring_nf

private lemma deriv_poly5_mul_gaussianMGFCore :
    deriv (fun t : ℝ => (15 * t + 10 * t ^ 3 + t ^ 5) * gaussianMGFCore t) =
      fun t : ℝ => (15 + 45 * t ^ 2 + 15 * t ^ 4 + t ^ 6) * gaussianMGFCore t := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by unfold gaussianMGFCore; fun_prop)]
  rw [deriv_gaussianMGFCore]
  simp only [differentiableAt_const, differentiableAt_fun_id, Nat.cast_ofNat,
    DifferentiableAt.fun_pow, DifferentiableAt.const_mul, DifferentiableAt.add,
    deriv_fun_add, deriv_const_mul, deriv_fun_pow, Nat.add_one_sub_one, pow_one,
    deriv_id'', mul_one]
  have hpoly :
      deriv (fun t : ℝ => 15 * t + 10 * t ^ 3 + t ^ 5) t =
        15 + 30 * t ^ 2 + 5 * t ^ 4 := by
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    have hlin : deriv (fun y : ℝ => 15 * y) t = 15 := by
      rw [deriv_const_mul_field (u := (15 : ℝ)) (v := fun y : ℝ => y) (x := t)]
      simp [deriv_id'']
    have hcubic : deriv (fun y : ℝ => 10 * y ^ 3) t = 30 * t ^ 2 := by
      rw [deriv_const_mul_field (u := (10 : ℝ)) (v := fun y : ℝ => y ^ 3) (x := t)]
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    have hquint : deriv (fun y : ℝ => y ^ 5) t = 5 * t ^ 4 := by
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    simpa [hlin, hcubic, hquint]
  rw [hpoly]
  ring_nf

lemma gaussianReal_moment_four :
    (∫ x : ℝ, x ^ 4 ∂(gaussianReal 0 1)) = (3 : ℝ) := by
  calc
    (∫ x : ℝ, x ^ 4 ∂(gaussianReal 0 1))
        = iteratedDeriv 4 (mgf (fun x : ℝ => x) (gaussianReal 0 1)) 0 := by
          rw [iteratedDeriv_mgf_zero] <;> simp
    _ = 3 := by
      rw [mgf_fun_id_gaussianReal]
      simp only [zero_mul, zero_add, NNReal.coe_one, one_mul]
      change iteratedDeriv 4 gaussianMGFCore 0 = 3
      rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
      rw [deriv_gaussianMGFCore, deriv_t_mul_gaussianMGFCore,
        deriv_poly2_mul_gaussianMGFCore, deriv_poly3_mul_gaussianMGFCore]
      simp [gaussianMGFCore]

lemma gaussianReal_moment_six :
    (∫ x : ℝ, x ^ 6 ∂(gaussianReal 0 1)) = (15 : ℝ) := by
  calc
    (∫ x : ℝ, x ^ 6 ∂(gaussianReal 0 1))
        = iteratedDeriv 6 (mgf (fun x : ℝ => x) (gaussianReal 0 1)) 0 := by
          rw [iteratedDeriv_mgf_zero] <;> simp
    _ = 15 := by
      rw [mgf_fun_id_gaussianReal]
      simp only [zero_mul, zero_add, NNReal.coe_one, one_mul]
      change iteratedDeriv 6 gaussianMGFCore 0 = 15
      rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ,
        iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
      rw [deriv_gaussianMGFCore, deriv_t_mul_gaussianMGFCore,
        deriv_poly2_mul_gaussianMGFCore, deriv_poly3_mul_gaussianMGFCore,
        deriv_poly4_mul_gaussianMGFCore, deriv_poly5_mul_gaussianMGFCore]
      simp [gaussianMGFCore]

lemma gaussianPDFReal_zero_one (x : ℝ) :
    gaussianPDFReal 0 1 x =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2) := by
  simp [gaussianPDFReal]

private lemma gaussian_weighted_moment_from_probability (k : ℕ) (m : ℝ)
    (hm : (∫ x : ℝ, x ^ k ∂(gaussianReal 0 1)) = m) :
    (∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ k) =
      Real.sqrt (2 * Real.pi) * m := by
  have hprob :=
    integral_gaussianReal_eq_integral_smul
      (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
      (f := fun x : ℝ => x ^ k) (by norm_num : (1 : ℝ≥0) ≠ 0)
  rw [hm] at hprob
  rw [show (∫ x : ℝ, gaussianPDFReal 0 1 x • x ^ k) =
      (Real.sqrt (2 * Real.pi))⁻¹ *
        ∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ k by
        simp_rw [gaussianPDFReal_zero_one, smul_eq_mul]
        rw [← integral_const_mul]
        apply integral_congr_ae
        refine ae_of_all _ ?_
        intro x
        ring] at hprob
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hsqrt_ne : Real.sqrt (2 * Real.pi) ≠ 0 := hsqrt_pos.ne'
  calc
    (∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ k)
        = Real.sqrt (2 * Real.pi) *
            ((Real.sqrt (2 * Real.pi))⁻¹ *
              ∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ k) := by
          field_simp [hsqrt_ne]
    _ = Real.sqrt (2 * Real.pi) * m := by rw [← hprob]

lemma gaussian_weighted_moment_four :
    (∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ 4) =
      3 * Real.sqrt (2 * Real.pi) := by
  calc
    (∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ 4)
        = Real.sqrt (2 * Real.pi) * 3 :=
          gaussian_weighted_moment_from_probability 4 3 gaussianReal_moment_four
    _ = 3 * Real.sqrt (2 * Real.pi) := by ring

lemma gaussian_weighted_moment_six :
    (∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ 6) =
      15 * Real.sqrt (2 * Real.pi) := by
  calc
    (∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ 6)
        = Real.sqrt (2 * Real.pi) * 15 :=
          gaussian_weighted_moment_from_probability 6 15 gaussianReal_moment_six
    _ = 15 * Real.sqrt (2 * Real.pi) := by ring

end

/-!
# Second-order saddle core definitions

This file defines the universal Gaussian correction polynomial and the scalar
second-order correction appearing after integrating its even moments.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval

noncomputable section

lemma saddleSecondPoly_quarticCoeff_norm_le_scale
    {b b3 b4 : ℝ → ℝ} {r : ℝ} (hb : 0 < b r) :
    ‖(b4 r : ℂ) / (24 * (b r : ℂ) ^ 2)‖ ≤
      (1 / 24 : ℝ) * saddleCorrectionScale b b3 b4 r := by
  have hb2pos : 0 < (b r) ^ 2 := sq_pos_of_pos hb
  have hb3nonneg : 0 ≤ (b3 r) ^ 2 / (b r) ^ 3 := by
    exact div_nonneg (sq_nonneg _) (by positivity)
  calc
    ‖(b4 r : ℂ) / (24 * (b r : ℂ) ^ 2)‖
        = |b4 r| / (24 * (b r) ^ 2) := by
          simp [norm_pow, Real.norm_eq_abs, abs_of_pos hb]
    _ = (1 / 24 : ℝ) * (|b4 r| / (b r) ^ 2) := by ring
    _ ≤ (1 / 24 : ℝ) * (|b4 r| / (b r) ^ 2 + (b3 r) ^ 2 / (b r) ^ 3) := by
          exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hb3nonneg)
            (by norm_num)
    _ = (1 / 24 : ℝ) * saddleCorrectionScale b b3 b4 r := by rfl

lemma saddleSecondPoly_sexticCoeff_norm_le_scale
    {b b3 b4 : ℝ → ℝ} {r : ℝ} (hb : 0 < b r) :
    ‖(((b3 r) ^ 2 : ℝ) : ℂ) / (72 * (b r : ℂ) ^ 3)‖ ≤
      (1 / 72 : ℝ) * saddleCorrectionScale b b3 b4 r := by
  have hb2nonneg : 0 ≤ |b4 r| / (b r) ^ 2 := by
    exact div_nonneg (abs_nonneg _) (sq_nonneg _)
  calc
    ‖(((b3 r) ^ 2 : ℝ) : ℂ) / (72 * (b r : ℂ) ^ 3)‖
        = (b3 r) ^ 2 / (72 * (b r) ^ 3) := by
          simp [norm_pow, Real.norm_eq_abs, abs_of_pos hb]
    _ = (1 / 72 : ℝ) * ((b3 r) ^ 2 / (b r) ^ 3) := by ring
    _ ≤ (1 / 72 : ℝ) * (|b4 r| / (b r) ^ 2 + (b3 r) ^ 2 / (b r) ^ 3) := by
          exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hb2nonneg)
            (by norm_num)
    _ = (1 / 72 : ℝ) * saddleCorrectionScale b b3 b4 r := by rfl

private lemma gaussian_weighted_integrable_zero :
    Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) := by
  simpa [show (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) =
      (fun x : ℝ => Real.exp (-(1 / 2 : ℝ) * x ^ 2)) by
        funext x
        ring_nf] using
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2))

private lemma gaussian_weighted_integrable_four :
    Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ 4) := by
  simpa [show (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ 4) =
      (fun x : ℝ => x ^ 4 * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) by
        funext x
        ring_nf] using
    (integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (-1 : ℝ) < 4))

private lemma gaussian_weighted_integrable_six :
    Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ 6) := by
  simpa [show (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ 6) =
      (fun x : ℝ => x ^ 6 * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) by
        funext x
        ring_nf] using
    (integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (-1 : ℝ) < 6))

private lemma gaussian_complex_integrable_zero :
    Integrable (fun x : ℝ => Complex.exp (-(x ^ 2) / 2)) := by
  simpa using (gaussian_weighted_integrable_zero.ofReal (𝕜 := ℂ))

private lemma gaussian_complex_integrable_four :
    Integrable (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4) := by
  simpa using (gaussian_weighted_integrable_four.ofReal (𝕜 := ℂ))

private lemma gaussian_complex_integrable_six :
    Integrable (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6) := by
  simpa using (gaussian_weighted_integrable_six.ofReal (𝕜 := ℂ))

/-- The odd cubic Gaussian moment vanishes on every symmetric window. -/
lemma gaussian_window_weighted_moment_three_eq_zero (L : ℝ) :
    (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 3) = 0 := by
  let g : ℝ → ℂ := fun x => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 3
  have hcomp : (∫ x in -L..L, g (-x)) = ∫ x in -L..L, g x := by
    simpa only [neg_neg] using
      (intervalIntegral.integral_comp_neg (f := g) (a := -L) (b := L))
  have hodd : (fun x : ℝ => g (-x)) = fun x : ℝ => -g x := by
    funext x
    simp [g]
    ring
  rw [hodd] at hcomp
  rw [intervalIntegral.integral_neg] at hcomp
  have hzero : (∫ x in -L..L, g x) = -(∫ x in -L..L, g x) := hcomp.symm
  have htwo : (2 : ℂ) * (∫ x in -L..L, g x) = 0 := by
    calc
      (2 : ℂ) * (∫ x in -L..L, g x) =
          (∫ x in -L..L, g x) + (∫ x in -L..L, g x) := by ring
      _ = -(∫ x in -L..L, g x) + (∫ x in -L..L, g x) := by
            nth_rw 1 [hzero]
      _ = 0 := by ring
  simpa [g] using (mul_eq_zero.mp htwo).resolve_left (by norm_num : (2 : ℂ) ≠ 0)

private lemma gaussian_complex_weighted_moment_four :
    (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4) =
      (3 * Real.sqrt (2 * Real.pi) : ℂ) := by
  set_option backward.isDefEq.respectTransparency false in
    rw [show (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4) =
        (fun x : ℝ => ((Real.exp (-(x ^ 2) / 2) * x ^ 4 : ℝ) : ℂ)) by
          funext x
          simp]
    rw [integral_complex_ofReal
      (f := fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ 4)
      (μ := (volume : Measure ℝ))]
    exact_mod_cast gaussian_weighted_moment_four

private lemma _saddle_SecondOrderCore_gaussian_complex_weighted_moment_six :
    (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6) =
      (15 * Real.sqrt (2 * Real.pi) : ℂ) := by
  set_option backward.isDefEq.respectTransparency false in
    rw [show (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6) =
        (fun x : ℝ => ((Real.exp (-(x ^ 2) / 2) * x ^ 6 : ℝ) : ℂ)) by
          funext x
          simp]
    rw [integral_complex_ofReal
      (f := fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ 6)
      (μ := (volume : Measure ℝ))]
    exact_mod_cast gaussian_weighted_moment_six

/-- The scalar correction is exactly the normalized quartic and sextic Gaussian moments. -/
theorem saddleCorrection_eq_gaussian_even_moments (b b3 b4 : ℝ → ℝ) (r : ℝ) :
    (saddleCorrection b b3 b4 r : ℂ) =
      (1 / Real.sqrt (2 * Real.pi) : ℂ) *
        (((b4 r : ℂ) / (24 * (b r : ℂ) ^ 2)) *
            (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4) -
          ((((b3 r) ^ 2 : ℝ) : ℂ) / (72 * (b r : ℂ) ^ 3)) *
            (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)) := by
  rw [gaussian_complex_weighted_moment_four, _saddle_SecondOrderCore_gaussian_complex_weighted_moment_six]
  simp [saddleCorrection]
  have hsqrtπ_ne : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hsqrt2_ne : (Real.sqrt (2 : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  field_simp [hsqrtπ_ne, hsqrt2_ne]
  ring_nf

/--
Symmetric-window version of the polynomial expansion.  The cubic contribution
vanishes exactly on `[-L,L]`.
-/
theorem gaussian_window_integral_saddleSecondPoly
    (b b3 b4 : ℝ → ℝ) (r L : ℝ) :
    (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) *
        saddleSecondPoly b b3 b4 r x) =
      (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2)) +
        ((b4 r : ℂ) / (24 * (b r : ℂ) ^ 2)) *
          (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4) -
        ((((b3 r) ^ 2 : ℝ) : ℂ) / (72 * (b r : ℂ) ^ 3)) *
          (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6) := by
  let A : ℂ := Complex.I * ((b3 r : ℂ) / (6 * (Real.sqrt (b r) : ℂ) ^ 3))
  let D : ℂ := (b4 r : ℂ) / (24 * (b r : ℂ) ^ 2)
  let E : ℂ := (((b3 r) ^ 2 : ℝ) : ℂ) / (72 * (b r : ℂ) ^ 3)
  let F0 : ℝ → ℂ := fun x => Complex.exp (-(x ^ 2) / 2)
  let F3 : ℝ → ℂ := fun x => A * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 3)
  let F4 : ℝ → ℂ := fun x => D * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4)
  let F6 : ℝ → ℂ := fun x => E * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)
  have hpoly :
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * saddleSecondPoly b b3 b4 r x) =
        fun x : ℝ => (F0 - F3 + F4 - F6) x := by
    funext x
    simp [F0, F3, F4, F6, saddleSecondPoly, A, D, E]
    ring
  rw [hpoly]
  have hF0 : IntervalIntegrable F0 volume (-L) L := by
    have hcont : Continuous F0 := by
      unfold F0
      fun_prop
    exact hcont.intervalIntegrable _ _
  have hF3 : IntervalIntegrable F3 volume (-L) L := by
    have hcont : Continuous F3 := by
      unfold F3
      fun_prop
    exact hcont.intervalIntegrable _ _
  have hF4 : IntervalIntegrable F4 volume (-L) L := by
    have hcont : Continuous F4 := by
      unfold F4
      fun_prop
    exact hcont.intervalIntegrable _ _
  have hF6 : IntervalIntegrable F6 volume (-L) L := by
    have hcont : Continuous F6 := by
      unfold F6
      fun_prop
    exact hcont.intervalIntegrable _ _
  have hF03 : IntervalIntegrable (fun x : ℝ => F0 x - F3 x) volume (-L) L := hF0.sub hF3
  have hF034 : IntervalIntegrable (fun x : ℝ => F0 x - F3 x + F4 x) volume (-L) L :=
    hF03.add hF4
  simp only [Pi.sub_apply, Pi.add_apply]
  rw [intervalIntegral.integral_sub hF034 hF6]
  rw [intervalIntegral.integral_add hF03 hF4]
  rw [intervalIntegral.integral_sub hF0 hF3]
  simp only [F0, F3, F4, F6]
  have hAeval :
      (∫ x in -L..L, A * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 3)) =
        A * ∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 3 := by
    exact intervalIntegral.integral_const_mul A
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 3)
  have hDeval :
      (∫ x in -L..L, D * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4)) =
        D * ∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4 := by
    exact intervalIntegral.integral_const_mul D
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4)
  have hEeval :
      (∫ x in -L..L, E * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)) =
        E * ∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6 := by
    exact intervalIntegral.integral_const_mul E
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)
  rw [hAeval, hDeval, hEeval, gaussian_window_weighted_moment_three_eq_zero]
  simp [A, D, E]

/-- Expanding symmetric windows exhaust an integrable function on the line. -/
lemma intervalIntegral_tendsto_integral_symmetric
    {g : ℝ → ℂ} (hg : Integrable g) {L : ℕ → ℝ}
    (hL : Tendsto L atTop atTop) :
    Tendsto (fun n : ℕ => ∫ x in -(L n)..(L n), g x)
      atTop (𝓝 (∫ x : ℝ, g x)) := by
  simpa using
    (intervalIntegral_tendsto_integral (μ := volume) hg
      (tendsto_neg_atTop_atBot.comp hL) hL)

/-- Fourth weighted Gaussian windows converge to the full fourth moment. -/
lemma gaussian_window_weighted_moment_four_tendsto
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop) :
    Tendsto
      (fun n : ℕ =>
        ∫ x in -(L n)..(L n),
          Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4)
      atTop
      (𝓝 (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4)) :=
  intervalIntegral_tendsto_integral_symmetric gaussian_complex_integrable_four hL

/-- Sixth weighted Gaussian windows converge to the full sixth moment. -/
lemma gaussian_window_weighted_moment_six_tendsto
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop) :
    Tendsto
      (fun n : ℕ =>
        ∫ x in -(L n)..(L n),
          Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)
      atTop
      (𝓝 (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)) :=
  intervalIntegral_tendsto_integral_symmetric gaussian_complex_integrable_six hL

/-- A crude one-sided Gaussian tail bound, enough for relative saddle-window estimates. -/
lemma gaussian_tail_Ioi_le_exp {L : ℝ} (hL : 1 ≤ L) :
    (∫ x in Set.Ioi L, Real.exp (-(x ^ 2) / 2)) ≤
      Real.exp (-(L ^ 2) / 2) := by
  have hderiv : ∀ x ∈ Set.Ici L,
      HasDerivAt (fun y : ℝ => -Real.exp (-(y ^ 2) / 2))
        (x * Real.exp (-(x ^ 2) / 2)) x := by
    intro x _hx
    have h1 : HasDerivAt (fun y : ℝ => -(y ^ 2) / 2) (-x) x := by
      convert ((hasDerivAt_pow 2 x).neg.div_const 2) using 1
      ring
    have h2 := h1.exp.neg
    convert h2 using 1
    ring
  have hint : IntegrableOn (fun x : ℝ => x * Real.exp (-(x ^ 2) / 2)) (Set.Ioi L) := by
    have hbase : Integrable (fun x : ℝ => x * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) :=
      integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
    convert hbase.integrableOn using 1
    funext x
    ring_nf
  have htop : Tendsto (fun y : ℝ => -Real.exp (-(y ^ 2) / 2)) atTop (𝓝 0) := by
    have hsq : Tendsto (fun y : ℝ => -(y ^ 2) / 2) atTop atBot := by
      have hpow : Tendsto (fun y : ℝ => y ^ 2) atTop atTop :=
        tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
      have hmul : Tendsto (fun y : ℝ => (-(1 / 2 : ℝ)) * y ^ 2) atTop atBot :=
        (tendsto_const_mul_atBot_of_neg (by norm_num : (-(1 / 2 : ℝ)) < 0)).mpr hpow
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
    have hexp : Tendsto (fun y : ℝ => Real.exp (-(y ^ 2) / 2)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp hsq
    simpa using hexp.neg
  have hxeq : (∫ x in Set.Ioi L, x * Real.exp (-(x ^ 2) / 2)) =
      Real.exp (-(L ^ 2) / 2) := by
    convert integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htop using 1
    ring
  have hleftint : IntegrableOn (fun x : ℝ => Real.exp (-(x ^ 2) / 2)) (Set.Ioi L) := by
    have hbase : Integrable (fun x : ℝ => Real.exp (-(1 / 2 : ℝ) * x ^ 2)) :=
      integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
    convert hbase.integrableOn using 1
    funext x
    ring_nf
  have hmono : (∫ x in Set.Ioi L, Real.exp (-(x ^ 2) / 2)) ≤
      ∫ x in Set.Ioi L, x * Real.exp (-(x ^ 2) / 2) := by
    refine setIntegral_mono_on hleftint hint measurableSet_Ioi ?_
    intro x hx
    have hxL : L < x := hx
    have hx1 : 1 ≤ x := le_trans hL (le_of_lt hxL)
    have hnon : 0 ≤ Real.exp (-(x ^ 2) / 2) := (Real.exp_pos _).le
    calc
      Real.exp (-(x ^ 2) / 2) = 1 * Real.exp (-(x ^ 2) / 2) := by simp
      _ ≤ x * Real.exp (-(x ^ 2) / 2) :=
            mul_le_mul_of_nonneg_right hx1 hnon
  simpa [hxeq] using hmono

/--
The normalized zeroth Gaussian window differs from `1` by at most a constant
times the one-sided Gaussian boundary exponential.
-/
lemma gaussian_window_zero_error_norm_le_exp {L : ℝ} (hL : 1 ≤ L) :
    ‖(1 / Real.sqrt (2 * Real.pi) : ℂ) *
        (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2)) - 1‖
      ≤ (2 / Real.sqrt (2 * Real.pi)) * Real.exp (-(L ^ 2) / 2) := by
  let g : ℝ → ℂ := fun x => Complex.exp (-(x ^ 2) / 2)
  let tail : ℂ := ∫ x in Set.Ioi L, g x
  let leftTail : ℂ := ∫ x in Set.Iic (-L), g x
  let window : ℂ := ∫ x in -L..L, g x
  let invG : ℂ := (1 / Real.sqrt (2 * Real.pi) : ℂ)
  have hLnonneg : 0 ≤ L := le_trans zero_le_one hL
  have hg : Integrable g := by
    simpa [g] using gaussian_complex_integrable_zero
  have hleftInt : IntegrableOn g (Set.Iic (-L)) := hg.integrableOn
  have hrightFromLeft : IntegrableOn g (Set.Ioi (-L)) := hg.integrableOn
  have hrightInt : IntegrableOn g (Set.Ioi L) := hg.integrableOn
  have hsplitFull :
      leftTail + (∫ x in Set.Ioi (-L), g x) = ∫ x : ℝ, g x := by
    simpa [leftTail] using
      (intervalIntegral.integral_Iic_add_Ioi (f := g) (b := -L) hleftInt hrightFromLeft)
  have hsplitRight :
      window + tail = ∫ x in Set.Ioi (-L), g x := by
    simpa [window, tail] using
      (intervalIntegral.integral_interval_add_Ioi
        (f := g) (a := -L) (b := L) hrightFromLeft hrightInt)
  have hfull :
      (∫ x : ℝ, g x) = leftTail + window + tail := by
    calc
      (∫ x : ℝ, g x) = leftTail + (∫ x in Set.Ioi (-L), g x) := hsplitFull.symm
      _ = leftTail + (window + tail) := by rw [← hsplitRight]
      _ = leftTail + window + tail := by ring
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hinv_full : invG * (∫ x : ℝ, g x) = 1 := by
    rw [gaussian_integral_half]
    change (1 / (Real.sqrt (2 * Real.pi) : ℂ)) *
        (Real.sqrt (2 * Real.pi) : ℂ) = 1
    field_simp [Complex.ofReal_ne_zero.mpr hsqrt_pos.ne']
  have hdiff :
      invG * window - 1 = -invG * (leftTail + tail) := by
    rw [← hinv_full, hfull]
    ring
  have hrightNorm :
      ‖tail‖ ≤ Real.exp (-(L ^ 2) / 2) := by
    calc
      ‖tail‖ ≤ ∫ x in Set.Ioi L, ‖g x‖ := by
        simpa [tail] using
          (norm_integral_le_integral_norm
            (f := fun x : ℝ => g x) (μ := volume.restrict (Set.Ioi L)))
      _ = ∫ x in Set.Ioi L, Real.exp (-(x ^ 2) / 2) := by
        apply integral_congr_ae
        refine ae_of_all _ ?_
        intro x
        simp [g, Complex.norm_exp, sq]
      _ ≤ Real.exp (-(L ^ 2) / 2) := gaussian_tail_Ioi_le_exp hL
  have hleftEq : leftTail = tail := by
    have hcomp :
        (∫ x in Set.Iic (-L), g (-x)) = ∫ x in Set.Ioi L, g x := by
      simpa only [neg_neg] using (integral_comp_neg_Iic (c := -L) (f := g))
    have heven :
        (∫ x in Set.Iic (-L), g (-x)) = ∫ x in Set.Iic (-L), g x := by
      apply setIntegral_congr_fun measurableSet_Iic
      intro x _hx
      simp [g]
    simpa [leftTail, tail] using heven.symm.trans hcomp
  have hleftNorm :
      ‖leftTail‖ ≤ Real.exp (-(L ^ 2) / 2) := by
    simpa [hleftEq] using hrightNorm
  calc
    ‖invG * window - 1‖ = ‖-invG * (leftTail + tail)‖ := by rw [hdiff]
    _ ≤ ‖invG‖ * (‖leftTail‖ + ‖tail‖) := by
      rw [norm_mul, norm_neg]
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
    _ ≤ ‖invG‖ *
        (Real.exp (-(L ^ 2) / 2) + Real.exp (-(L ^ 2) / 2)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hleftNorm hrightNorm) (norm_nonneg _)
    _ = (2 / Real.sqrt (2 * Real.pi)) * Real.exp (-(L ^ 2) / 2) := by
      have hinv_norm : ‖invG‖ = 1 / Real.sqrt (2 * Real.pi) := by
        dsimp [invG]
        rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hsqrt_pos]
      rw [hinv_norm]
      ring

end

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-!
# Third-order saddle core definitions

This file extends the universal second-order Gaussian correction polynomial by
the order-`b^{-2}` terms in the Hayman saddle expansion.
-/

open Complex Filter Asymptotics MeasureTheory ProbabilityTheory
open scoped Topology Real NNReal ENNReal Interval

noncomputable section

private lemma saddleCorrectionScale_le_saddleThirdCorrectionScale
    {b b3 b4 b5 b6 : ℝ → ℝ} {r : ℝ} (hb : 0 < b r) :
    saddleCorrectionScale b b3 b4 r ≤
      saddleThirdCorrectionScale b b3 b4 b5 b6 r := by
  dsimp [saddleThirdCorrectionScale]
  have h1 : 0 ≤ |b6 r| / (b r) ^ 3 := by positivity
  have h2 : 0 ≤ |b3 r * b5 r| / (b r) ^ 4 := by positivity
  have h3 : 0 ≤ (b4 r) ^ 2 / (b r) ^ 4 := by positivity
  have h4 : 0 ≤ (b3 r) ^ 2 * |b4 r| / (b r) ^ 5 := by positivity
  have h5 : 0 ≤ (b3 r) ^ 4 / (b r) ^ 6 := by positivity
  nlinarith

private lemma saddleThirdScale_term_b6_le
    {b b3 b4 b5 b6 : ℝ → ℝ} {r : ℝ} (hb : 0 < b r) :
    |b6 r| / (b r) ^ 3 ≤ saddleThirdCorrectionScale b b3 b4 b5 b6 r := by
  dsimp [saddleThirdCorrectionScale]
  have h0 : 0 ≤ saddleCorrectionScale b b3 b4 r := by
    dsimp [saddleCorrectionScale]
    positivity
  dsimp [saddleCorrectionScale] at h0
  have h2 : 0 ≤ |b3 r * b5 r| / (b r) ^ 4 := by positivity
  have h3 : 0 ≤ (b4 r) ^ 2 / (b r) ^ 4 := by positivity
  have h4 : 0 ≤ (b3 r) ^ 2 * |b4 r| / (b r) ^ 5 := by positivity
  have h5 : 0 ≤ (b3 r) ^ 4 / (b r) ^ 6 := by positivity
  nlinarith

private lemma saddleThirdScale_term_b3b5_le
    {b b3 b4 b5 b6 : ℝ → ℝ} {r : ℝ} (hb : 0 < b r) :
    |b3 r * b5 r| / (b r) ^ 4 ≤
      saddleThirdCorrectionScale b b3 b4 b5 b6 r := by
  dsimp [saddleThirdCorrectionScale]
  have h0 : 0 ≤ saddleCorrectionScale b b3 b4 r := by
    dsimp [saddleCorrectionScale]
    positivity
  dsimp [saddleCorrectionScale] at h0
  have h1 : 0 ≤ |b6 r| / (b r) ^ 3 := by positivity
  have h3 : 0 ≤ (b4 r) ^ 2 / (b r) ^ 4 := by positivity
  have h4 : 0 ≤ (b3 r) ^ 2 * |b4 r| / (b r) ^ 5 := by positivity
  have h5 : 0 ≤ (b3 r) ^ 4 / (b r) ^ 6 := by positivity
  nlinarith

private lemma saddleThirdScale_term_b4sq_le
    {b b3 b4 b5 b6 : ℝ → ℝ} {r : ℝ} (hb : 0 < b r) :
    (b4 r) ^ 2 / (b r) ^ 4 ≤ saddleThirdCorrectionScale b b3 b4 b5 b6 r := by
  dsimp [saddleThirdCorrectionScale]
  have h0 : 0 ≤ saddleCorrectionScale b b3 b4 r := by
    dsimp [saddleCorrectionScale]
    positivity
  dsimp [saddleCorrectionScale] at h0
  have h1 : 0 ≤ |b6 r| / (b r) ^ 3 := by positivity
  have h2 : 0 ≤ |b3 r * b5 r| / (b r) ^ 4 := by positivity
  have h4 : 0 ≤ (b3 r) ^ 2 * |b4 r| / (b r) ^ 5 := by positivity
  have h5 : 0 ≤ (b3 r) ^ 4 / (b r) ^ 6 := by positivity
  nlinarith

private lemma saddleThirdScale_term_b3sqb4_le
    {b b3 b4 b5 b6 : ℝ → ℝ} {r : ℝ} (hb : 0 < b r) :
    (b3 r) ^ 2 * |b4 r| / (b r) ^ 5 ≤
      saddleThirdCorrectionScale b b3 b4 b5 b6 r := by
  dsimp [saddleThirdCorrectionScale]
  have h0 : 0 ≤ saddleCorrectionScale b b3 b4 r := by
    dsimp [saddleCorrectionScale]
    positivity
  dsimp [saddleCorrectionScale] at h0
  have h1 : 0 ≤ |b6 r| / (b r) ^ 3 := by positivity
  have h2 : 0 ≤ |b3 r * b5 r| / (b r) ^ 4 := by positivity
  have h3 : 0 ≤ (b4 r) ^ 2 / (b r) ^ 4 := by positivity
  have h5 : 0 ≤ (b3 r) ^ 4 / (b r) ^ 6 := by positivity
  nlinarith

private lemma saddleThirdScale_term_b3four_le
    {b b3 b4 b5 b6 : ℝ → ℝ} {r : ℝ} (hb : 0 < b r) :
    (b3 r) ^ 4 / (b r) ^ 6 ≤ saddleThirdCorrectionScale b b3 b4 b5 b6 r := by
  dsimp [saddleThirdCorrectionScale]
  have h0 : 0 ≤ saddleCorrectionScale b b3 b4 r := by
    dsimp [saddleCorrectionScale]
    positivity
  dsimp [saddleCorrectionScale] at h0
  have h1 : 0 ≤ |b6 r| / (b r) ^ 3 := by positivity
  have h2 : 0 ≤ |b3 r * b5 r| / (b r) ^ 4 := by positivity
  have h3 : 0 ≤ (b4 r) ^ 2 / (b r) ^ 4 := by positivity
  have h4 : 0 ≤ (b3 r) ^ 2 * |b4 r| / (b r) ^ 5 := by positivity
  nlinarith

lemma saddleThirdPoly_quarticCoeff_norm_le_scale
    {b b3 b4 b5 b6 : ℝ → ℝ} {r : ℝ} (hb : 0 < b r) :
    ‖(b4 r : ℂ) / (24 * (b r : ℂ) ^ 2)‖ ≤
      (1 / 24 : ℝ) * saddleThirdCorrectionScale b b3 b4 b5 b6 r := by
  calc
    ‖(b4 r : ℂ) / (24 * (b r : ℂ) ^ 2)‖
        ≤ (1 / 24 : ℝ) * saddleCorrectionScale b b3 b4 r :=
          saddleSecondPoly_quarticCoeff_norm_le_scale (b := b) (b3 := b3)
            (b4 := b4) (r := r) hb
    _ ≤ (1 / 24 : ℝ) * saddleThirdCorrectionScale b b3 b4 b5 b6 r :=
          mul_le_mul_of_nonneg_left
            (saddleCorrectionScale_le_saddleThirdCorrectionScale
              (b := b) (b3 := b3) (b4 := b4) (b5 := b5) (b6 := b6) hb)
            (by norm_num)

lemma saddleThirdPoly_sexticB3Coeff_norm_le_scale
    {b b3 b4 b5 b6 : ℝ → ℝ} {r : ℝ} (hb : 0 < b r) :
    ‖(((b3 r) ^ 2 : ℝ) : ℂ) / (72 * (b r : ℂ) ^ 3)‖ ≤
      (1 / 72 : ℝ) * saddleThirdCorrectionScale b b3 b4 b5 b6 r := by
  calc
    ‖(((b3 r) ^ 2 : ℝ) : ℂ) / (72 * (b r : ℂ) ^ 3)‖
        ≤ (1 / 72 : ℝ) * saddleCorrectionScale b b3 b4 r :=
          saddleSecondPoly_sexticCoeff_norm_le_scale (b := b) (b3 := b3)
            (b4 := b4) (r := r) hb
    _ ≤ (1 / 72 : ℝ) * saddleThirdCorrectionScale b b3 b4 b5 b6 r :=
          mul_le_mul_of_nonneg_left
            (saddleCorrectionScale_le_saddleThirdCorrectionScale
              (b := b) (b3 := b3) (b4 := b4) (b5 := b5) (b6 := b6) hb)
            (by norm_num)

lemma saddleThirdPoly_b6Coeff_norm_le_scale
    {b b3 b4 b5 b6 : ℝ → ℝ} {r : ℝ} (hb : 0 < b r) :
    ‖(b6 r : ℂ) / (720 * (b r : ℂ) ^ 3)‖ ≤
      (1 / 720 : ℝ) * saddleThirdCorrectionScale b b3 b4 b5 b6 r := by
  calc
    ‖(b6 r : ℂ) / (720 * (b r : ℂ) ^ 3)‖
        = |b6 r| / (720 * (b r) ^ 3) := by
          simp [norm_pow, Real.norm_eq_abs, abs_of_pos hb]
    _ = (1 / 720 : ℝ) * (|b6 r| / (b r) ^ 3) := by ring
    _ ≤ (1 / 720 : ℝ) * saddleThirdCorrectionScale b b3 b4 b5 b6 r :=
          mul_le_mul_of_nonneg_left
            (saddleThirdScale_term_b6_le
              (b := b) (b3 := b3) (b4 := b4) (b5 := b5) (b6 := b6) hb)
            (by norm_num)

lemma saddleThirdPoly_b3b5Coeff_norm_le_scale
    {b b3 b4 b5 b6 : ℝ → ℝ} {r : ℝ} (hb : 0 < b r) :
    ‖(((b3 r * b5 r : ℝ) : ℂ) / (720 * (b r : ℂ) ^ 4))‖ ≤
      (1 / 720 : ℝ) * saddleThirdCorrectionScale b b3 b4 b5 b6 r := by
  calc
    ‖(((b3 r * b5 r : ℝ) : ℂ) / (720 * (b r : ℂ) ^ 4))‖
        = |b3 r * b5 r| / (720 * (b r) ^ 4) := by
          simp [norm_pow, Real.norm_eq_abs, abs_of_pos hb]
    _ = (1 / 720 : ℝ) * (|b3 r * b5 r| / (b r) ^ 4) := by ring
    _ ≤ (1 / 720 : ℝ) * saddleThirdCorrectionScale b b3 b4 b5 b6 r :=
          mul_le_mul_of_nonneg_left
            (saddleThirdScale_term_b3b5_le
              (b := b) (b3 := b3) (b4 := b4) (b5 := b5) (b6 := b6) hb)
            (by norm_num)

lemma saddleThirdPoly_b4sqCoeff_norm_le_scale
    {b b3 b4 b5 b6 : ℝ → ℝ} {r : ℝ} (hb : 0 < b r) :
    ‖((((b4 r) ^ 2 : ℝ) : ℂ) / (1152 * (b r : ℂ) ^ 4))‖ ≤
      (1 / 1152 : ℝ) * saddleThirdCorrectionScale b b3 b4 b5 b6 r := by
  calc
    ‖((((b4 r) ^ 2 : ℝ) : ℂ) / (1152 * (b r : ℂ) ^ 4))‖
        = (b4 r) ^ 2 / (1152 * (b r) ^ 4) := by
          simp [norm_pow, Real.norm_eq_abs, abs_of_pos hb]
    _ = (1 / 1152 : ℝ) * ((b4 r) ^ 2 / (b r) ^ 4) := by ring
    _ ≤ (1 / 1152 : ℝ) * saddleThirdCorrectionScale b b3 b4 b5 b6 r :=
          mul_le_mul_of_nonneg_left
            (saddleThirdScale_term_b4sq_le
              (b := b) (b3 := b3) (b4 := b4) (b5 := b5) (b6 := b6) hb)
            (by norm_num)

lemma saddleThirdPoly_b3sqb4Coeff_norm_le_scale
    {b b3 b4 b5 b6 : ℝ → ℝ} {r : ℝ} (hb : 0 < b r) :
    ‖((((b3 r) ^ 2 * b4 r : ℝ) : ℂ) / (1728 * (b r : ℂ) ^ 5))‖ ≤
      (1 / 1728 : ℝ) * saddleThirdCorrectionScale b b3 b4 b5 b6 r := by
  have hsq : 0 ≤ (b3 r) ^ 2 := sq_nonneg _
  calc
    ‖((((b3 r) ^ 2 * b4 r : ℝ) : ℂ) / (1728 * (b r : ℂ) ^ 5))‖
        = ((b3 r) ^ 2 * |b4 r|) / (1728 * (b r) ^ 5) := by
          simp [norm_pow, Real.norm_eq_abs, abs_of_pos hb, abs_mul, abs_of_nonneg hsq]
    _ = (1 / 1728 : ℝ) * (((b3 r) ^ 2 * |b4 r|) / (b r) ^ 5) := by ring
    _ ≤ (1 / 1728 : ℝ) * saddleThirdCorrectionScale b b3 b4 b5 b6 r :=
          mul_le_mul_of_nonneg_left
            (saddleThirdScale_term_b3sqb4_le
              (b := b) (b3 := b3) (b4 := b4) (b5 := b5) (b6 := b6) hb)
            (by norm_num)

lemma saddleThirdPoly_b3fourCoeff_norm_le_scale
    {b b3 b4 b5 b6 : ℝ → ℝ} {r : ℝ} (hb : 0 < b r) :
    ‖((((b3 r) ^ 4 : ℝ) : ℂ) / (31104 * (b r : ℂ) ^ 6))‖ ≤
      (1 / 31104 : ℝ) * saddleThirdCorrectionScale b b3 b4 b5 b6 r := by
  have hpow : 0 ≤ (b3 r) ^ 4 := by positivity
  have habs_pow : |b3 r| ^ 4 = (b3 r) ^ 4 := by
    rw [← abs_pow, abs_of_nonneg hpow]
  calc
    ‖((((b3 r) ^ 4 : ℝ) : ℂ) / (31104 * (b r : ℂ) ^ 6))‖
        = (b3 r) ^ 4 / (31104 * (b r) ^ 6) := by
          simp [norm_pow, Real.norm_eq_abs, abs_of_pos hb, abs_of_nonneg hpow,
            habs_pow]
    _ = (1 / 31104 : ℝ) * (((b3 r) ^ 4) / (b r) ^ 6) := by ring
    _ ≤ (1 / 31104 : ℝ) * saddleThirdCorrectionScale b b3 b4 b5 b6 r :=
          mul_le_mul_of_nonneg_left
            (saddleThirdScale_term_b3four_le
              (b := b) (b3 := b3) (b4 := b4) (b5 := b5) (b6 := b6) hb)
            (by norm_num)

private lemma deriv_gaussianMGFCoreThird :
    deriv gaussianMGFCoreThird = fun t : ℝ => t * gaussianMGFCoreThird t := by
  ext t
  unfold gaussianMGFCoreThird
  rw [_root_.deriv_exp (by fun_prop)]
  simp only [deriv_div_const, differentiableAt_const, differentiableAt_fun_id, Nat.cast_ofNat,
    DifferentiableAt.fun_pow, deriv_fun_mul, deriv_const', zero_mul, deriv_fun_pow,
    Nat.add_one_sub_one, pow_one, deriv_id'', mul_one, zero_add]
  ring

private lemma deriv_t_mul_gaussianMGFCoreThird :
    deriv (fun t : ℝ => t * gaussianMGFCoreThird t) =
      fun t : ℝ => (1 + t ^ 2) * gaussianMGFCoreThird t := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by unfold gaussianMGFCoreThird; fun_prop)]
  rw [deriv_gaussianMGFCoreThird]
  simp
  ring_nf

private lemma deriv_poly2_mul_gaussianMGFCoreThird :
    deriv (fun t : ℝ => (1 + t ^ 2) * gaussianMGFCoreThird t) =
      fun t : ℝ => (3 * t + t ^ 3) * gaussianMGFCoreThird t := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by unfold gaussianMGFCoreThird; fun_prop)]
  rw [deriv_gaussianMGFCoreThird]
  simp only [differentiableAt_const, differentiableAt_fun_id, Nat.cast_ofNat,
    DifferentiableAt.fun_pow, DifferentiableAt.add, deriv_fun_add, deriv_const',
    deriv_fun_pow, Nat.add_one_sub_one, pow_one, deriv_id'', mul_one, zero_add]
  ring_nf

private lemma deriv_poly3_mul_gaussianMGFCoreThird :
    deriv (fun t : ℝ => (3 * t + t ^ 3) * gaussianMGFCoreThird t) =
      fun t : ℝ => (3 + 6 * t ^ 2 + t ^ 4) * gaussianMGFCoreThird t := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by unfold gaussianMGFCoreThird; fun_prop)]
  rw [deriv_gaussianMGFCoreThird]
  simp only [differentiableAt_const, differentiableAt_fun_id, Nat.cast_ofNat,
    DifferentiableAt.fun_pow, DifferentiableAt.const_mul, DifferentiableAt.add,
    deriv_fun_add, deriv_const_mul, deriv_fun_pow, Nat.add_one_sub_one, pow_one,
    deriv_id'', mul_one]
  have hpoly : deriv (fun t : ℝ => 3 * t + t ^ 3) t = 3 + 3 * t ^ 2 := by
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    have hlin : deriv (fun y : ℝ => 3 * y) t = 3 := by
      rw [deriv_const_mul_field (u := (3 : ℝ)) (v := fun y : ℝ => y) (x := t)]
      simp [deriv_id'']
    have hpow : deriv (fun y : ℝ => y ^ 3) t = 3 * t ^ 2 := by
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    simpa [hlin, hpow]
  rw [hpoly]
  ring_nf

private lemma deriv_poly4_mul_gaussianMGFCoreThird :
    deriv (fun t : ℝ => (3 + 6 * t ^ 2 + t ^ 4) * gaussianMGFCoreThird t) =
      fun t : ℝ => (15 * t + 10 * t ^ 3 + t ^ 5) * gaussianMGFCoreThird t := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by unfold gaussianMGFCoreThird; fun_prop)]
  rw [deriv_gaussianMGFCoreThird]
  simp only [differentiableAt_const, differentiableAt_fun_id, Nat.cast_ofNat,
    DifferentiableAt.fun_pow, DifferentiableAt.const_mul, DifferentiableAt.add,
    deriv_fun_add, deriv_const', deriv_const_mul, deriv_fun_pow, Nat.add_one_sub_one,
    pow_one, deriv_id'', mul_one, zero_add]
  have hpoly :
      deriv (fun t : ℝ => 3 + 6 * t ^ 2 + t ^ 4) t =
        12 * t + 4 * t ^ 3 := by
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    have hconst : deriv (fun _ : ℝ => (3 : ℝ)) t = 0 := by
      rw [deriv_const']
    have hquad : deriv (fun y : ℝ => 6 * y ^ 2) t = 12 * t := by
      rw [deriv_const_mul_field (u := (6 : ℝ)) (v := fun y : ℝ => y ^ 2) (x := t)]
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    have hquart : deriv (fun y : ℝ => y ^ 4) t = 4 * t ^ 3 := by
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    simpa [hconst, hquad, hquart]
  rw [hpoly]
  ring_nf

private lemma deriv_poly5_mul_gaussianMGFCoreThird :
    deriv (fun t : ℝ => (15 * t + 10 * t ^ 3 + t ^ 5) * gaussianMGFCoreThird t) =
      fun t : ℝ => (15 + 45 * t ^ 2 + 15 * t ^ 4 + t ^ 6) *
        gaussianMGFCoreThird t := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by unfold gaussianMGFCoreThird; fun_prop)]
  rw [deriv_gaussianMGFCoreThird]
  simp only [differentiableAt_const, differentiableAt_fun_id, Nat.cast_ofNat,
    DifferentiableAt.fun_pow, DifferentiableAt.const_mul, DifferentiableAt.add,
    deriv_fun_add, deriv_const_mul, deriv_fun_pow, Nat.add_one_sub_one, pow_one,
    deriv_id'', mul_one]
  have hpoly :
      deriv (fun t : ℝ => 15 * t + 10 * t ^ 3 + t ^ 5) t =
        15 + 30 * t ^ 2 + 5 * t ^ 4 := by
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    have hlin : deriv (fun y : ℝ => 15 * y) t = 15 := by
      rw [deriv_const_mul_field (u := (15 : ℝ)) (v := fun y : ℝ => y) (x := t)]
      simp [deriv_id'']
    have hcubic : deriv (fun y : ℝ => 10 * y ^ 3) t = 30 * t ^ 2 := by
      rw [deriv_const_mul_field (u := (10 : ℝ)) (v := fun y : ℝ => y ^ 3) (x := t)]
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    have hquint : deriv (fun y : ℝ => y ^ 5) t = 5 * t ^ 4 := by
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    simpa [hlin, hcubic, hquint]
  rw [hpoly]
  ring_nf

private lemma deriv_poly6_mul_gaussianMGFCoreThird :
    deriv (fun t : ℝ => (15 + 45 * t ^ 2 + 15 * t ^ 4 + t ^ 6) *
        gaussianMGFCoreThird t) =
      fun t : ℝ => (105 * t + 105 * t ^ 3 + 21 * t ^ 5 + t ^ 7) *
        gaussianMGFCoreThird t := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by unfold gaussianMGFCoreThird; fun_prop)]
  rw [deriv_gaussianMGFCoreThird]
  rw [show deriv (fun t : ℝ => 15 + 45 * t ^ 2 + 15 * t ^ 4 + t ^ 6) t =
      90 * t + 60 * t ^ 3 + 6 * t ^ 5 by
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    simp only [deriv_const', deriv_const_mul, deriv_fun_mul, deriv_fun_pow,
      differentiableAt_fun_id, differentiableAt_const, DifferentiableAt.fun_pow,
      DifferentiableAt.const_mul, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one,
      deriv_id'', mul_one, zero_mul, add_zero, zero_add]
    ring_nf]
  ring_nf

private lemma deriv_poly7_mul_gaussianMGFCoreThird :
    deriv (fun t : ℝ => (105 * t + 105 * t ^ 3 + 21 * t ^ 5 + t ^ 7) *
        gaussianMGFCoreThird t) =
      fun t : ℝ => (105 + 420 * t ^ 2 + 210 * t ^ 4 + 28 * t ^ 6 + t ^ 8) *
        gaussianMGFCoreThird t := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by unfold gaussianMGFCoreThird; fun_prop)]
  rw [deriv_gaussianMGFCoreThird]
  have hderiv :
      deriv (fun t : ℝ => 105 * t + 105 * t ^ 3 + 21 * t ^ 5 + t ^ 7) t =
        105 + 315 * t ^ 2 + 105 * t ^ 4 + 7 * t ^ 6 := by
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    have hlin : deriv (fun y : ℝ => 105 * y) t = 105 := by
      rw [deriv_const_mul_field (u := (105 : ℝ)) (v := fun y : ℝ => y) (x := t)]
      simp [deriv_id'']
    have hcubic : deriv (fun y : ℝ => 105 * y ^ 3) t = 315 * t ^ 2 := by
      rw [deriv_const_mul_field (u := (105 : ℝ)) (v := fun y : ℝ => y ^ 3) (x := t)]
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    have hquint : deriv (fun y : ℝ => 21 * y ^ 5) t = 105 * t ^ 4 := by
      rw [deriv_const_mul_field (u := (21 : ℝ)) (v := fun y : ℝ => y ^ 5) (x := t)]
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    have hsept : deriv (fun y : ℝ => y ^ 7) t = 7 * t ^ 6 := by
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    simpa [hlin, hcubic, hquint, hsept]
  rw [hderiv]
  ring_nf

private lemma deriv_poly8_mul_gaussianMGFCoreThird :
    deriv (fun t : ℝ =>
        (105 + 420 * t ^ 2 + 210 * t ^ 4 + 28 * t ^ 6 + t ^ 8) *
          gaussianMGFCoreThird t) =
      fun t : ℝ => (945 * t + 1260 * t ^ 3 + 378 * t ^ 5 + 36 * t ^ 7 + t ^ 9) *
        gaussianMGFCoreThird t := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by unfold gaussianMGFCoreThird; fun_prop)]
  rw [deriv_gaussianMGFCoreThird]
  rw [show deriv (fun t : ℝ =>
      105 + 420 * t ^ 2 + 210 * t ^ 4 + 28 * t ^ 6 + t ^ 8) t =
      840 * t + 840 * t ^ 3 + 168 * t ^ 5 + 8 * t ^ 7 by
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    simp only [deriv_const', deriv_const_mul, deriv_fun_mul, deriv_fun_pow,
      differentiableAt_fun_id, differentiableAt_const, DifferentiableAt.fun_pow,
      DifferentiableAt.const_mul, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one,
      deriv_id'', mul_one, zero_mul, add_zero, zero_add]
    ring_nf]
  ring_nf

private lemma deriv_poly9_mul_gaussianMGFCoreThird :
    deriv (fun t : ℝ =>
        (945 * t + 1260 * t ^ 3 + 378 * t ^ 5 + 36 * t ^ 7 + t ^ 9) *
          gaussianMGFCoreThird t) =
      fun t : ℝ =>
        (945 + 4725 * t ^ 2 + 3150 * t ^ 4 + 630 * t ^ 6 + 45 * t ^ 8 + t ^ 10) *
          gaussianMGFCoreThird t := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by unfold gaussianMGFCoreThird; fun_prop)]
  rw [deriv_gaussianMGFCoreThird]
  have hderiv :
      deriv (fun t : ℝ =>
        945 * t + 1260 * t ^ 3 + 378 * t ^ 5 + 36 * t ^ 7 + t ^ 9) t =
        945 + 3780 * t ^ 2 + 1890 * t ^ 4 + 252 * t ^ 6 + 9 * t ^ 8 := by
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    have hlin : deriv (fun y : ℝ => 945 * y) t = 945 := by
      rw [deriv_const_mul_field (u := (945 : ℝ)) (v := fun y : ℝ => y) (x := t)]
      simp [deriv_id'']
    have hcubic : deriv (fun y : ℝ => 1260 * y ^ 3) t = 3780 * t ^ 2 := by
      rw [deriv_const_mul_field (u := (1260 : ℝ)) (v := fun y : ℝ => y ^ 3) (x := t)]
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    have hquint : deriv (fun y : ℝ => 378 * y ^ 5) t = 1890 * t ^ 4 := by
      rw [deriv_const_mul_field (u := (378 : ℝ)) (v := fun y : ℝ => y ^ 5) (x := t)]
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    have hsept : deriv (fun y : ℝ => 36 * y ^ 7) t = 252 * t ^ 6 := by
      rw [deriv_const_mul_field (u := (36 : ℝ)) (v := fun y : ℝ => y ^ 7) (x := t)]
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    have hnine : deriv (fun y : ℝ => y ^ 9) t = 9 * t ^ 8 := by
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    simpa [hlin, hcubic, hquint, hsept, hnine]
  rw [hderiv]
  ring_nf

private lemma deriv_poly10_mul_gaussianMGFCoreThird :
    deriv (fun t : ℝ =>
        (945 + 4725 * t ^ 2 + 3150 * t ^ 4 + 630 * t ^ 6 + 45 * t ^ 8 + t ^ 10) *
          gaussianMGFCoreThird t) =
      fun t : ℝ =>
        (10395 * t + 17325 * t ^ 3 + 6930 * t ^ 5 + 990 * t ^ 7 + 55 * t ^ 9 +
            t ^ 11) *
          gaussianMGFCoreThird t := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by unfold gaussianMGFCoreThird; fun_prop)]
  rw [deriv_gaussianMGFCoreThird]
  rw [show deriv (fun t : ℝ =>
      945 + 4725 * t ^ 2 + 3150 * t ^ 4 + 630 * t ^ 6 + 45 * t ^ 8 + t ^ 10) t =
      9450 * t + 12600 * t ^ 3 + 3780 * t ^ 5 + 360 * t ^ 7 + 10 * t ^ 9 by
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    simp only [deriv_const', deriv_const_mul, deriv_fun_mul, deriv_fun_pow,
      differentiableAt_fun_id, differentiableAt_const, DifferentiableAt.fun_pow,
      DifferentiableAt.const_mul, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one,
      deriv_id'', mul_one, zero_mul, add_zero, zero_add]
    ring_nf]
  ring_nf

private lemma deriv_poly11_mul_gaussianMGFCoreThird :
    deriv (fun t : ℝ =>
        (10395 * t + 17325 * t ^ 3 + 6930 * t ^ 5 + 990 * t ^ 7 + 55 * t ^ 9 +
            t ^ 11) *
          gaussianMGFCoreThird t) =
      fun t : ℝ =>
        (10395 + 62370 * t ^ 2 + 51975 * t ^ 4 + 13860 * t ^ 6 +
            1485 * t ^ 8 + 66 * t ^ 10 + t ^ 12) *
          gaussianMGFCoreThird t := by
  ext t
  rw [deriv_fun_mul (by fun_prop) (by unfold gaussianMGFCoreThird; fun_prop)]
  rw [deriv_gaussianMGFCoreThird]
  have hderiv :
      deriv (fun t : ℝ =>
        10395 * t + 17325 * t ^ 3 + 6930 * t ^ 5 + 990 * t ^ 7 + 55 * t ^ 9 +
            t ^ 11) t =
        10395 + 51975 * t ^ 2 + 34650 * t ^ 4 + 6930 * t ^ 6 + 495 * t ^ 8 +
          11 * t ^ 10 := by
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    have hlin : deriv (fun y : ℝ => 10395 * y) t = 10395 := by
      rw [deriv_const_mul_field (u := (10395 : ℝ)) (v := fun y : ℝ => y) (x := t)]
      simp [deriv_id'']
    have hcubic : deriv (fun y : ℝ => 17325 * y ^ 3) t = 51975 * t ^ 2 := by
      rw [deriv_const_mul_field (u := (17325 : ℝ)) (v := fun y : ℝ => y ^ 3) (x := t)]
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    have hquint : deriv (fun y : ℝ => 6930 * y ^ 5) t = 34650 * t ^ 4 := by
      rw [deriv_const_mul_field (u := (6930 : ℝ)) (v := fun y : ℝ => y ^ 5) (x := t)]
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    have hsept : deriv (fun y : ℝ => 990 * y ^ 7) t = 6930 * t ^ 6 := by
      rw [deriv_const_mul_field (u := (990 : ℝ)) (v := fun y : ℝ => y ^ 7) (x := t)]
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    have hnine : deriv (fun y : ℝ => 55 * y ^ 9) t = 495 * t ^ 8 := by
      rw [deriv_const_mul_field (u := (55 : ℝ)) (v := fun y : ℝ => y ^ 9) (x := t)]
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    have heleven : deriv (fun y : ℝ => y ^ 11) t = 11 * t ^ 10 := by
      rw [deriv_fun_pow (by fun_prop)]
      rw [deriv_id'']
      ring
    simpa [hlin, hcubic, hquint, hsept, hnine, heleven]
  rw [hderiv]
  ring_nf

private lemma gaussianReal_moment_eight :
    (∫ x : ℝ, x ^ 8 ∂(gaussianReal 0 1)) = (105 : ℝ) := by
  calc
    (∫ x : ℝ, x ^ 8 ∂(gaussianReal 0 1))
        = iteratedDeriv 8 (mgf (fun x : ℝ => x) (gaussianReal 0 1)) 0 := by
          rw [iteratedDeriv_mgf_zero] <;> simp
    _ = 105 := by
      rw [mgf_fun_id_gaussianReal]
      simp only [zero_mul, zero_add, NNReal.coe_one, one_mul]
      change iteratedDeriv 8 gaussianMGFCoreThird 0 = 105
      rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ,
        iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ,
        iteratedDeriv_succ, iteratedDeriv_one]
      rw [deriv_gaussianMGFCoreThird, deriv_t_mul_gaussianMGFCoreThird,
        deriv_poly2_mul_gaussianMGFCoreThird, deriv_poly3_mul_gaussianMGFCoreThird,
        deriv_poly4_mul_gaussianMGFCoreThird, deriv_poly5_mul_gaussianMGFCoreThird,
        deriv_poly6_mul_gaussianMGFCoreThird, deriv_poly7_mul_gaussianMGFCoreThird]
      simp [gaussianMGFCoreThird]

private lemma gaussianReal_moment_ten :
    (∫ x : ℝ, x ^ 10 ∂(gaussianReal 0 1)) = (945 : ℝ) := by
  calc
    (∫ x : ℝ, x ^ 10 ∂(gaussianReal 0 1))
        = iteratedDeriv 10 (mgf (fun x : ℝ => x) (gaussianReal 0 1)) 0 := by
          rw [iteratedDeriv_mgf_zero] <;> simp
    _ = 945 := by
      rw [mgf_fun_id_gaussianReal]
      simp only [zero_mul, zero_add, NNReal.coe_one, one_mul]
      change iteratedDeriv 10 gaussianMGFCoreThird 0 = 945
      rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ,
        iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ,
        iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
      rw [deriv_gaussianMGFCoreThird, deriv_t_mul_gaussianMGFCoreThird,
        deriv_poly2_mul_gaussianMGFCoreThird, deriv_poly3_mul_gaussianMGFCoreThird,
        deriv_poly4_mul_gaussianMGFCoreThird, deriv_poly5_mul_gaussianMGFCoreThird,
        deriv_poly6_mul_gaussianMGFCoreThird, deriv_poly7_mul_gaussianMGFCoreThird,
        deriv_poly8_mul_gaussianMGFCoreThird, deriv_poly9_mul_gaussianMGFCoreThird]
      simp [gaussianMGFCoreThird]

private lemma gaussianReal_moment_twelve :
    (∫ x : ℝ, x ^ 12 ∂(gaussianReal 0 1)) = (10395 : ℝ) := by
  calc
    (∫ x : ℝ, x ^ 12 ∂(gaussianReal 0 1))
        = iteratedDeriv 12 (mgf (fun x : ℝ => x) (gaussianReal 0 1)) 0 := by
          rw [iteratedDeriv_mgf_zero] <;> simp
    _ = 10395 := by
      rw [mgf_fun_id_gaussianReal]
      simp only [zero_mul, zero_add, NNReal.coe_one, one_mul]
      change iteratedDeriv 12 gaussianMGFCoreThird 0 = 10395
      rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ,
        iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ,
        iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ,
        iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one]
      rw [deriv_gaussianMGFCoreThird, deriv_t_mul_gaussianMGFCoreThird,
        deriv_poly2_mul_gaussianMGFCoreThird, deriv_poly3_mul_gaussianMGFCoreThird,
        deriv_poly4_mul_gaussianMGFCoreThird, deriv_poly5_mul_gaussianMGFCoreThird,
        deriv_poly6_mul_gaussianMGFCoreThird, deriv_poly7_mul_gaussianMGFCoreThird,
        deriv_poly8_mul_gaussianMGFCoreThird, deriv_poly9_mul_gaussianMGFCoreThird,
        deriv_poly10_mul_gaussianMGFCoreThird, deriv_poly11_mul_gaussianMGFCoreThird]
      simp [gaussianMGFCoreThird]

private lemma gaussian_weighted_moment_from_probability_third (k : ℕ) (m : ℝ)
    (hm : (∫ x : ℝ, x ^ k ∂(gaussianReal 0 1)) = m) :
    (∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ k) =
      Real.sqrt (2 * Real.pi) * m := by
  have hprob :=
    integral_gaussianReal_eq_integral_smul
      (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
      (f := fun x : ℝ => x ^ k) (by norm_num : (1 : ℝ≥0) ≠ 0)
  rw [hm] at hprob
  rw [show (∫ x : ℝ, gaussianPDFReal 0 1 x • x ^ k) =
      (Real.sqrt (2 * Real.pi))⁻¹ *
        ∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ k by
        simp_rw [gaussianPDFReal_zero_one, smul_eq_mul]
        rw [← integral_const_mul]
        apply integral_congr_ae
        refine ae_of_all _ ?_
        intro x
        ring] at hprob
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hsqrt_ne : Real.sqrt (2 * Real.pi) ≠ 0 := hsqrt_pos.ne'
  calc
    (∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ k)
        = Real.sqrt (2 * Real.pi) *
            ((Real.sqrt (2 * Real.pi))⁻¹ *
              ∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ k) := by
          field_simp [hsqrt_ne]
    _ = Real.sqrt (2 * Real.pi) * m := by rw [← hprob]

lemma gaussian_weighted_moment_eight :
    (∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ 8) =
      105 * Real.sqrt (2 * Real.pi) := by
  calc
    (∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ 8)
        = Real.sqrt (2 * Real.pi) * 105 :=
          gaussian_weighted_moment_from_probability_third 8 105 gaussianReal_moment_eight
    _ = 105 * Real.sqrt (2 * Real.pi) := by ring

lemma gaussian_weighted_moment_ten :
    (∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ 10) =
      945 * Real.sqrt (2 * Real.pi) := by
  calc
    (∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ 10)
        = Real.sqrt (2 * Real.pi) * 945 :=
          gaussian_weighted_moment_from_probability_third 10 945 gaussianReal_moment_ten
    _ = 945 * Real.sqrt (2 * Real.pi) := by ring

lemma gaussian_weighted_moment_twelve :
    (∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ 12) =
      10395 * Real.sqrt (2 * Real.pi) := by
  calc
    (∫ x : ℝ, Real.exp (-(x ^ 2) / 2) * x ^ 12)
        = Real.sqrt (2 * Real.pi) * 10395 :=
          gaussian_weighted_moment_from_probability_third 12 10395
          gaussianReal_moment_twelve
    _ = 10395 * Real.sqrt (2 * Real.pi) := by ring

private lemma gaussian_weighted_integrable_eight :
    Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ 8) := by
  simpa [show (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ 8) =
      (fun x : ℝ => x ^ 8 * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) by
        funext x
        ring_nf] using
    (integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (-1 : ℝ) < 8))

private lemma gaussian_weighted_integrable_ten :
    Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ 10) := by
  simpa [show (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ 10) =
      (fun x : ℝ => x ^ 10 * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) by
        funext x
        ring_nf] using
    (integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (-1 : ℝ) < 10))

private lemma gaussian_weighted_integrable_twelve :
    Integrable (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ 12) := by
  simpa [show (fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ 12) =
      (fun x : ℝ => x ^ 12 * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) by
        funext x
        ring_nf] using
    (integrable_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (-1 : ℝ) < 12))

private lemma gaussian_complex_integrable_eight :
    Integrable (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8) := by
  simpa using (gaussian_weighted_integrable_eight.ofReal (𝕜 := ℂ))

private lemma gaussian_complex_integrable_ten :
    Integrable (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 10) := by
  simpa using (gaussian_weighted_integrable_ten.ofReal (𝕜 := ℂ))

private lemma gaussian_complex_integrable_twelve :
    Integrable (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 12) := by
  simpa using (gaussian_weighted_integrable_twelve.ofReal (𝕜 := ℂ))

private lemma _saddle_ThirdOrderCore_gaussian_complex_weighted_moment_six :
    (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6) =
      (15 * Real.sqrt (2 * Real.pi) : ℂ) := by
  set_option backward.isDefEq.respectTransparency false in
    rw [show (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6) =
        (fun x : ℝ => ((Real.exp (-(x ^ 2) / 2) * x ^ 6 : ℝ) : ℂ)) by
          funext x
          simp]
    rw [integral_complex_ofReal
      (f := fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ 6)
      (μ := (volume : Measure ℝ))]
    exact_mod_cast gaussian_weighted_moment_six

private lemma gaussian_complex_weighted_moment_eight :
    (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8) =
      (105 * Real.sqrt (2 * Real.pi) : ℂ) := by
  set_option backward.isDefEq.respectTransparency false in
    rw [show (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8) =
        (fun x : ℝ => ((Real.exp (-(x ^ 2) / 2) * x ^ 8 : ℝ) : ℂ)) by
          funext x
          simp]
    rw [integral_complex_ofReal
      (f := fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ 8)
      (μ := (volume : Measure ℝ))]
    exact_mod_cast gaussian_weighted_moment_eight

private lemma gaussian_complex_weighted_moment_ten :
    (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 10) =
      (945 * Real.sqrt (2 * Real.pi) : ℂ) := by
  set_option backward.isDefEq.respectTransparency false in
    rw [show (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 10) =
        (fun x : ℝ => ((Real.exp (-(x ^ 2) / 2) * x ^ 10 : ℝ) : ℂ)) by
          funext x
          simp]
    rw [integral_complex_ofReal
      (f := fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ 10)
      (μ := (volume : Measure ℝ))]
    exact_mod_cast gaussian_weighted_moment_ten

private lemma gaussian_complex_weighted_moment_twelve :
    (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 12) =
      (10395 * Real.sqrt (2 * Real.pi) : ℂ) := by
  set_option backward.isDefEq.respectTransparency false in
    rw [show (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 12) =
        (fun x : ℝ => ((Real.exp (-(x ^ 2) / 2) * x ^ 12 : ℝ) : ℂ)) by
          funext x
          simp]
    rw [integral_complex_ofReal
      (f := fun x : ℝ => Real.exp (-(x ^ 2) / 2) * x ^ 12)
      (μ := (volume : Measure ℝ))]
    exact_mod_cast gaussian_weighted_moment_twelve

lemma gaussian_window_weighted_moment_five_eq_zero (L : ℝ) :
    (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 5) = 0 := by
  let g : ℝ → ℂ := fun x => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 5
  have hcomp : (∫ x in -L..L, g (-x)) = ∫ x in -L..L, g x := by
    simpa only [neg_neg] using
      (intervalIntegral.integral_comp_neg (f := g) (a := -L) (b := L))
  have hodd : (fun x : ℝ => g (-x)) = fun x : ℝ => -g x := by
    funext x
    simp [g]
    ring
  rw [hodd] at hcomp
  rw [intervalIntegral.integral_neg] at hcomp
  have hzero : (∫ x in -L..L, g x) = -(∫ x in -L..L, g x) := hcomp.symm
  have htwo : (2 : ℂ) * (∫ x in -L..L, g x) = 0 := by
    calc
      (2 : ℂ) * (∫ x in -L..L, g x) =
          (∫ x in -L..L, g x) + (∫ x in -L..L, g x) := by ring
      _ = -(∫ x in -L..L, g x) + (∫ x in -L..L, g x) := by
            nth_rw 1 [hzero]
      _ = 0 := by ring
  simpa [g] using (mul_eq_zero.mp htwo).resolve_left (by norm_num : (2 : ℂ) ≠ 0)

lemma gaussian_window_weighted_moment_seven_eq_zero (L : ℝ) :
    (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 7) = 0 := by
  let g : ℝ → ℂ := fun x => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 7
  have hcomp : (∫ x in -L..L, g (-x)) = ∫ x in -L..L, g x := by
    simpa only [neg_neg] using
      (intervalIntegral.integral_comp_neg (f := g) (a := -L) (b := L))
  have hodd : (fun x : ℝ => g (-x)) = fun x : ℝ => -g x := by
    funext x
    simp [g]
    ring
  rw [hodd] at hcomp
  rw [intervalIntegral.integral_neg] at hcomp
  have hzero : (∫ x in -L..L, g x) = -(∫ x in -L..L, g x) := hcomp.symm
  have htwo : (2 : ℂ) * (∫ x in -L..L, g x) = 0 := by
    calc
      (2 : ℂ) * (∫ x in -L..L, g x) =
          (∫ x in -L..L, g x) + (∫ x in -L..L, g x) := by ring
      _ = -(∫ x in -L..L, g x) + (∫ x in -L..L, g x) := by
            nth_rw 1 [hzero]
      _ = 0 := by ring
  simpa [g] using (mul_eq_zero.mp htwo).resolve_left (by norm_num : (2 : ℂ) ≠ 0)

lemma gaussian_window_weighted_moment_nine_eq_zero (L : ℝ) :
    (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 9) = 0 := by
  let g : ℝ → ℂ := fun x => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 9
  have hcomp : (∫ x in -L..L, g (-x)) = ∫ x in -L..L, g x := by
    simpa only [neg_neg] using
      (intervalIntegral.integral_comp_neg (f := g) (a := -L) (b := L))
  have hodd : (fun x : ℝ => g (-x)) = fun x : ℝ => -g x := by
    funext x
    simp [g]
    ring
  rw [hodd] at hcomp
  rw [intervalIntegral.integral_neg] at hcomp
  have hzero : (∫ x in -L..L, g x) = -(∫ x in -L..L, g x) := hcomp.symm
  have htwo : (2 : ℂ) * (∫ x in -L..L, g x) = 0 := by
    calc
      (2 : ℂ) * (∫ x in -L..L, g x) =
          (∫ x in -L..L, g x) + (∫ x in -L..L, g x) := by ring
      _ = -(∫ x in -L..L, g x) + (∫ x in -L..L, g x) := by
            nth_rw 1 [hzero]
      _ = 0 := by ring
  simpa [g] using (mul_eq_zero.mp htwo).resolve_left (by norm_num : (2 : ℂ) ≠ 0)

lemma gaussian_window_weighted_moment_eight_tendsto
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop) :
    Tendsto
      (fun n : ℕ =>
        ∫ x in -(L n)..(L n),
          Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8)
      atTop
      (𝓝 (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8)) :=
  intervalIntegral_tendsto_integral_symmetric gaussian_complex_integrable_eight hL

lemma gaussian_window_weighted_moment_ten_tendsto
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop) :
    Tendsto
      (fun n : ℕ =>
        ∫ x in -(L n)..(L n),
          Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 10)
      atTop
      (𝓝 (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 10)) :=
  intervalIntegral_tendsto_integral_symmetric gaussian_complex_integrable_ten hL

lemma gaussian_window_weighted_moment_twelve_tendsto
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop) :
    Tendsto
      (fun n : ℕ =>
        ∫ x in -(L n)..(L n),
          Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 12)
      atTop
      (𝓝 (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 12)) :=
  intervalIntegral_tendsto_integral_symmetric gaussian_complex_integrable_twelve hL

/-- The third-order scalar correction is exactly the normalized even moments. -/
theorem saddleThirdCorrection_eq_gaussian_even_moments
    (b b3 b4 b5 b6 : ℝ → ℝ) (r : ℝ) :
    (saddleThirdCorrection b b3 b4 b5 b6 r : ℂ) =
      (1 / Real.sqrt (2 * Real.pi) : ℂ) *
        (-((b6 r : ℂ) / (720 * (b r : ℂ) ^ 3)) *
            (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)
          + (((b3 r * b5 r : ℝ) : ℂ) / (720 * (b r : ℂ) ^ 4)) *
            (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8)
          + ((((b4 r) ^ 2 : ℝ) : ℂ) / (1152 * (b r : ℂ) ^ 4)) *
            (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8)
          - (((((b3 r) ^ 2 * b4 r : ℝ) : ℂ) / (1728 * (b r : ℂ) ^ 5)) *
            (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 10))
          + ((((b3 r) ^ 4 : ℝ) : ℂ) / (31104 * (b r : ℂ) ^ 6)) *
            (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 12)) := by
  rw [_saddle_ThirdOrderCore_gaussian_complex_weighted_moment_six, gaussian_complex_weighted_moment_eight,
    gaussian_complex_weighted_moment_ten, gaussian_complex_weighted_moment_twelve]
  simp only [saddleThirdCorrection_apply, _root_.Complex.ofReal_add, _root_.Complex.ofReal_sub, _root_.Complex.ofReal_div, _root_.Complex.ofReal_neg,
    _root_.Complex.ofReal_mul, _root_.Complex.ofReal_ofNat, _root_.Complex.ofReal_pow, Nat.ofNat_nonneg, Real.sqrt_mul, one_div,
    mul_inv_rev, neg_mul]
  have hsqrt_ne : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  field_simp [hsqrt_ne]
  ring_nf

/--
Symmetric-window version of the third-order polynomial expansion.  The odd
terms of degrees `5`, `7`, and `9` vanish exactly on `[-L,L]`, as does the
cubic term already handled by the second-order window lemma.
-/
theorem gaussian_window_integral_saddleThirdPoly
    (b b3 b4 b5 b6 : ℝ → ℝ) (r L : ℝ) :
    (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) *
        saddleThirdPoly b b3 b4 b5 b6 r x) =
      (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2)) +
        ((b4 r : ℂ) / (24 * (b r : ℂ) ^ 2)) *
          (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4) -
        ((((b3 r) ^ 2 : ℝ) : ℂ) / (72 * (b r : ℂ) ^ 3)) *
          (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6) -
        ((b6 r : ℂ) / (720 * (b r : ℂ) ^ 3)) *
          (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6) +
        (((b3 r * b5 r : ℝ) : ℂ) / (720 * (b r : ℂ) ^ 4)) *
          (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8) +
        ((((b4 r) ^ 2 : ℝ) : ℂ) / (1152 * (b r : ℂ) ^ 4)) *
          (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8) -
        (((((b3 r) ^ 2 * b4 r : ℝ) : ℂ) / (1728 * (b r : ℂ) ^ 5)) *
          (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 10)) +
        ((((b3 r) ^ 4 : ℝ) : ℂ) / (31104 * (b r : ℂ) ^ 6)) *
          (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 12) := by
  let C5 : ℂ := Complex.I * ((b5 r : ℂ) /
    (120 * (Real.sqrt (b r) : ℂ) ^ 5))
  let C6 : ℂ := (b6 r : ℂ) / (720 * (b r : ℂ) ^ 3)
  let C7 : ℂ := Complex.I * (((b3 r * b4 r : ℝ) : ℂ) /
    (144 * (Real.sqrt (b r) : ℂ) ^ 3 * (b r : ℂ) ^ 2))
  let C8a : ℂ := ((b3 r * b5 r : ℝ) : ℂ) / (720 * (b r : ℂ) ^ 4)
  let C8b : ℂ := (((b4 r) ^ 2 : ℝ) : ℂ) / (1152 * (b r : ℂ) ^ 4)
  let C9 : ℂ := Complex.I * ((((b3 r) ^ 3 : ℝ) : ℂ) /
    (1296 * (Real.sqrt (b r) : ℂ) ^ 9))
  let C10 : ℂ := (((b3 r) ^ 2 * b4 r : ℝ) : ℂ) /
    (1728 * (b r : ℂ) ^ 5)
  let C12 : ℂ := (((b3 r) ^ 4 : ℝ) : ℂ) / (31104 * (b r : ℂ) ^ 6)
  let P2 : ℝ → ℂ := fun x =>
    Complex.exp (-(x ^ 2) / 2) * saddleSecondPoly b b3 b4 r x
  let F5 : ℝ → ℂ := fun x => C5 * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 5)
  let F6 : ℝ → ℂ := fun x => C6 * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)
  let F7 : ℝ → ℂ := fun x => C7 * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 7)
  let F8a : ℝ → ℂ := fun x => C8a * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8)
  let F8b : ℝ → ℂ := fun x => C8b * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8)
  let F9 : ℝ → ℂ := fun x => C9 * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 9)
  let F10 : ℝ → ℂ := fun x => C10 * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 10)
  let F12 : ℝ → ℂ := fun x => C12 * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 12)
  have hpoly :
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) *
        saddleThirdPoly b b3 b4 b5 b6 r x) =
        fun x : ℝ => (P2 + F5 - F6 - F7 + F8a + F8b + F9 - F10 + F12) x := by
    funext x
    simp [P2, F5, F6, F7, F8a, F8b, F9, F10, F12, C5, C6, C7, C8a, C8b,
      C9, C10, C12, saddleThirdPoly]
    ring
  rw [hpoly]
  have hP2 : IntervalIntegrable P2 volume (-L) L := by
    have hcont : Continuous P2 := by
      unfold P2 saddleSecondPoly
      fun_prop
    exact hcont.intervalIntegrable _ _
  have hF5 : IntervalIntegrable F5 volume (-L) L := by
    have hcont : Continuous F5 := by
      unfold F5
      fun_prop
    exact hcont.intervalIntegrable _ _
  have hF6 : IntervalIntegrable F6 volume (-L) L := by
    have hcont : Continuous F6 := by
      unfold F6
      fun_prop
    exact hcont.intervalIntegrable _ _
  have hF7 : IntervalIntegrable F7 volume (-L) L := by
    have hcont : Continuous F7 := by
      unfold F7
      fun_prop
    exact hcont.intervalIntegrable _ _
  have hF8a : IntervalIntegrable F8a volume (-L) L := by
    have hcont : Continuous F8a := by
      unfold F8a
      fun_prop
    exact hcont.intervalIntegrable _ _
  have hF8b : IntervalIntegrable F8b volume (-L) L := by
    have hcont : Continuous F8b := by
      unfold F8b
      fun_prop
    exact hcont.intervalIntegrable _ _
  have hF9 : IntervalIntegrable F9 volume (-L) L := by
    have hcont : Continuous F9 := by
      unfold F9
      fun_prop
    exact hcont.intervalIntegrable _ _
  have hF10 : IntervalIntegrable F10 volume (-L) L := by
    have hcont : Continuous F10 := by
      unfold F10
      fun_prop
    exact hcont.intervalIntegrable _ _
  have hF12 : IntervalIntegrable F12 volume (-L) L := by
    have hcont : Continuous F12 := by
      unfold F12
      fun_prop
    exact hcont.intervalIntegrable _ _
  have h25 : IntervalIntegrable (fun x : ℝ => P2 x + F5 x) volume (-L) L :=
    hP2.add hF5
  have h256 : IntervalIntegrable (fun x : ℝ => P2 x + F5 x - F6 x) volume (-L) L :=
    h25.sub hF6
  have h2567 :
      IntervalIntegrable (fun x : ℝ => P2 x + F5 x - F6 x - F7 x) volume (-L) L :=
    h256.sub hF7
  have h25678a :
      IntervalIntegrable (fun x : ℝ => P2 x + F5 x - F6 x - F7 x + F8a x)
        volume (-L) L := h2567.add hF8a
  have h25678ab :
      IntervalIntegrable (fun x : ℝ => P2 x + F5 x - F6 x - F7 x + F8a x + F8b x)
        volume (-L) L := h25678a.add hF8b
  have h25678ab9 :
      IntervalIntegrable
        (fun x : ℝ => P2 x + F5 x - F6 x - F7 x + F8a x + F8b x + F9 x)
        volume (-L) L := h25678ab.add hF9
  have h25678ab910 :
      IntervalIntegrable
        (fun x : ℝ => P2 x + F5 x - F6 x - F7 x + F8a x + F8b x + F9 x - F10 x)
        volume (-L) L := h25678ab9.sub hF10
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [intervalIntegral.integral_add h25678ab910 hF12]
  rw [intervalIntegral.integral_sub h25678ab9 hF10]
  rw [intervalIntegral.integral_add h25678ab hF9]
  rw [intervalIntegral.integral_add h25678a hF8b]
  rw [intervalIntegral.integral_add h2567 hF8a]
  rw [intervalIntegral.integral_sub h256 hF7]
  rw [intervalIntegral.integral_sub h25 hF6]
  rw [intervalIntegral.integral_add hP2 hF5]
  simp only [P2, F5, F6, F7, F8a, F8b, F9, F10, F12]
  rw [gaussian_window_integral_saddleSecondPoly]
  have h5eval :
      (∫ x in -L..L, C5 * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 5)) =
        C5 * ∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 5 := by
    exact intervalIntegral.integral_const_mul C5
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 5)
  have h6eval :
      (∫ x in -L..L, C6 * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)) =
        C6 * ∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6 := by
    exact intervalIntegral.integral_const_mul C6
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)
  have h7eval :
      (∫ x in -L..L, C7 * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 7)) =
        C7 * ∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 7 := by
    exact intervalIntegral.integral_const_mul C7
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 7)
  have h8aeval :
      (∫ x in -L..L, C8a * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8)) =
        C8a * ∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8 := by
    exact intervalIntegral.integral_const_mul C8a
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8)
  have h8beval :
      (∫ x in -L..L, C8b * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8)) =
        C8b * ∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8 := by
    exact intervalIntegral.integral_const_mul C8b
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8)
  have h9eval :
      (∫ x in -L..L, C9 * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 9)) =
        C9 * ∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 9 := by
    exact intervalIntegral.integral_const_mul C9
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 9)
  have h10eval :
      (∫ x in -L..L, C10 * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 10)) =
        C10 * ∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 10 := by
    exact intervalIntegral.integral_const_mul C10
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 10)
  have h12eval :
      (∫ x in -L..L, C12 * (Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 12)) =
        C12 * ∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 12 := by
    exact intervalIntegral.integral_const_mul C12
      (fun x : ℝ => Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 12)
  rw [h5eval, h6eval, h7eval, h8aeval, h8beval, h9eval, h10eval, h12eval]
  rw [gaussian_window_weighted_moment_five_eq_zero,
    gaussian_window_weighted_moment_seven_eq_zero,
    gaussian_window_weighted_moment_nine_eq_zero]
  simp [C5, C6, C7, C8a, C8b, C9, C10, C12]

end

/-!
# Third-order H-admissible wrapper

This is a clean add-on to the second-order `HAdmissible` interface.  It records
the fifth and sixth logarithmic saddle derivatives, the robust third-order
scale, and the local/tail hypotheses used by the third-order saddle layer.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval

noncomputable section

private lemma complex_isLittleO_of_norm_div_tendsto_zero
    (u : ℕ → ℂ) (c : ℕ → ℝ)
    (hcpos : ∀ᶠ n in atTop, 0 < c n)
    (h : Tendsto (fun n : ℕ => ‖u n‖ / c n) atTop (𝓝 0)) :
    u =o[atTop] (fun n : ℕ => (c n : ℂ)) := by
  rw [isLittleO_iff_tendsto']
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine Tendsto.congr' ?_ h
    filter_upwards [hcpos] with n hcn
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcn]
  · filter_upwards [hcpos] with n hcn hzero
    exact (hcn.ne' (Complex.ofReal_eq_zero.mp hzero)).elim

private lemma third_tail_isLittleO
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (h2 : SecondOrderHAdmissible hf)
    (h3 : ThirdOrderHAdmissible hf h2)
    (hr : SaddleSequence hf) :
    (fun n : ℕ =>
      (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
        saddleJt f hr.r (HAdmissible.Δ hf hr) n)
      =o[atTop]
    (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) := by
  rcases h3.tail_third_uniform with ⟨E, hE_nonneg, hdecay, htail⟩
  let K : ℝ := ‖((2 * Real.pi : ℂ)⁻¹)‖ * (2 * Real.pi)
  have hBpos : ∀ᶠ n in atTop, 0 < HAdmissible.B hf hr n := by
    simpa [HAdmissible.B] using hr.tendsTo.eventually hf.b_pos
  have hδ_nonneg : ∀ᶠ n in atTop, 0 ≤ HAdmissible.Δ hf hr n := by
    filter_upwards [hr.tendsTo.eventually hf.δ_pos] with n hδn
    exact hδn.le
  have hδπ : ∀ᶠ n in atTop, HAdmissible.Δ hf hr n ≤ Real.pi := by
    simpa [HAdmissible.Δ] using hr.tendsTo.eventually hf.δ_le_pi
  have hE_nonneg_seq : ∀ᶠ n in atTop, 0 ≤ E (hr.r n) := by
    simpa using hr.tendsTo.eventually hE_nonneg
  have htailSeq :
      ∀ᶠ n in atTop, ∀ θ : ℝ,
        HAdmissible.Δ hf hr n ≤ |θ| → |θ| ≤ Real.pi →
          ‖saddleG f hr.r n θ‖ ≤ E (hr.r n) := by
    filter_upwards [hr.tendsTo.eventually htail] with n htailn θ hδθ hθπ
    simpa [HAdmissible.Δ, saddleG] using htailn n θ hδθ hθπ
  have hCpos : ∀ᶠ n in atTop, 0 < h3.corrScale3 (hr.r n) := by
    simpa using hr.tendsTo.eventually h3.corrScale3_pos
  have hdecaySeq :
      Tendsto
        (fun n : ℕ =>
          Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) *
            E (hr.r n) / h3.corrScale3 (hr.r n))
        atTop (𝓝 0) := by
    simpa [HAdmissible.B] using hdecay.comp hr.tendsTo
  have hupper :
      Tendsto
        (fun n : ℕ =>
          K * (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) *
            E (hr.r n) / h3.corrScale3 (hr.r n)))
        atTop (𝓝 0) := by
    simpa using hdecaySeq.const_mul K
  have hbound :
      ∀ᶠ n in atTop,
        ‖(Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
            saddleJt f hr.r (HAdmissible.Δ hf hr) n‖ /
            h3.corrScale3 (hr.r n) ≤
          K * (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) *
            E (hr.r n) / h3.corrScale3 (hr.r n)) := by
    filter_upwards [hBpos, hδ_nonneg, hδπ, hE_nonneg_seq, htailSeq, hCpos] with
      n hBn hδn hδπn hEn htailn hCn
    have hJ : ‖saddleJt f hr.r (HAdmissible.Δ hf hr) n‖ ≤ K * E (hr.r n) := by
      simpa [saddleJt, saddleG, K] using
        saddleJtAt_norm_le_of_tail_bound f (hr.r n) (HAdmissible.Δ hf hr n)
          (E (hr.r n)) n hδn hδπn hEn
          (fun θ hδθ hθπ => htailn θ hδθ hθπ)
    have hsqrt_nonneg : 0 ≤ Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) :=
      Real.sqrt_nonneg _
    have hnorm :
        ‖(Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
            saddleJt f hr.r (HAdmissible.Δ hf hr) n‖ ≤
          Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) * (K * E (hr.r n)) := by
      calc
        ‖(Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
            saddleJt f hr.r (HAdmissible.Δ hf hr) n‖
            =
              Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) *
                ‖saddleJt f hr.r (HAdmissible.Δ hf hr) n‖ := by
                rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
                  abs_of_nonneg hsqrt_nonneg]
        _ ≤ Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) *
              (K * E (hr.r n)) :=
              mul_le_mul_of_nonneg_left hJ hsqrt_nonneg
    have hdiv := div_le_div_of_nonneg_right hnorm hCn.le
    calc
      ‖(Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
          saddleJt f hr.r (HAdmissible.Δ hf hr) n‖ / h3.corrScale3 (hr.r n)
          ≤ Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) *
              (K * E (hr.r n)) / h3.corrScale3 (hr.r n) := hdiv
      _ = K * (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) *
              E (hr.r n) / h3.corrScale3 (hr.r n)) := by ring
  have hnonneg :
      ∀ᶠ n in atTop,
        0 ≤ ‖(Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
            saddleJt f hr.r (HAdmissible.Δ hf hr) n‖ /
            h3.corrScale3 (hr.r n) := by
    filter_upwards [hCpos] with n hCn
    exact div_nonneg (norm_nonneg _) hCn.le
  have hnormdiv :
      Tendsto
        (fun n : ℕ =>
          ‖(Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
            saddleJt f hr.r (HAdmissible.Δ hf hr) n‖ /
            h3.corrScale3 (hr.r n))
        atTop (𝓝 0) :=
    squeeze_zero' hnonneg hbound hupper
  exact complex_isLittleO_of_norm_div_tendsto_zero _ _ hCpos hnormdiv

private lemma coeff_ratio_eq_scaled_saddleJ_eventually
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (hr : SaddleSequence hf) :
    (fun n : ℕ =>
      p.coeff n / saddleScale f hr.r (HAdmissible.B hf hr) n)
      =ᶠ[atTop]
    (fun n : ℕ =>
      (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
        (saddleJc f hr.r (HAdmissible.Δ hf hr) n +
          saddleJt f hr.r (HAdmissible.Δ hf hr) n)) := by
  have hrpos : ∀ᶠ n in atTop, 0 < hr.r n := by
    simpa using hr.tendsTo.eventually hf.r_pos
  have hdiff :
      ∀ᶠ n in atTop,
        DifferentiableOn ℂ f (Metric.closedBall 0 (hr.r n)) := by
    simpa using hr.tendsTo.eventually hf.differentiableOn
  have hfnz : ∀ᶠ n in atTop, f (hr.r n : ℂ) ≠ 0 := by
    filter_upwards [hr.tendsTo.eventually hf.f_pos] with n hpos
    exact f_ne_zero_of_re_pos hpos
  have hleft :
      ∀ᶠ n in atTop,
        IntervalIntegrable (saddleG f hr.r n) volume
          (-Real.pi) (-(HAdmissible.Δ hf hr n)) := by
    filter_upwards [hrpos, hdiff] with n hrn hdn
    simpa [saddleG] using
      saddleGAt_intervalIntegrable_of_differentiableOn_closedBall
        f (hr.r n) n (-Real.pi) (-(HAdmissible.Δ hf hr n)) hrn.le hdn
  have hcenter :
      ∀ᶠ n in atTop,
        IntervalIntegrable (saddleG f hr.r n) volume
          (-(HAdmissible.Δ hf hr n)) (HAdmissible.Δ hf hr n) := by
    filter_upwards [hrpos, hdiff] with n hrn hdn
    simpa [saddleG] using
      saddleGAt_intervalIntegrable_of_differentiableOn_closedBall
        f (hr.r n) n (-(HAdmissible.Δ hf hr n)) (HAdmissible.Δ hf hr n) hrn.le hdn
  have hright :
      ∀ᶠ n in atTop,
        IntervalIntegrable (saddleG f hr.r n) volume
          (HAdmissible.Δ hf hr n) Real.pi := by
    filter_upwards [hrpos, hdiff] with n hrn hdn
    simpa [saddleG] using
      saddleGAt_intervalIntegrable_of_differentiableOn_closedBall
        f (hr.r n) n (HAdmissible.Δ hf hr n) Real.pi hrn.le hdn
  have Hsplit :
      ∀ᶠ n in atTop,
        p.coeff n =
          saddlePref f hr.r n *
            (saddleJc f hr.r (HAdmissible.Δ hf hr) n +
              saddleJt f hr.r (HAdmissible.Δ hf hr) n) :=
    eventually_coeff_eq_saddle_split
      hr.r (HAdmissible.Δ hf hr) hf.hp hrpos hdiff hfnz hleft hcenter hright
  have hBpos : ∀ᶠ n in atTop, 0 < HAdmissible.B hf hr n := by
    simpa [HAdmissible.B] using hr.tendsTo.eventually hf.b_pos
  have Hnz :
      ∀ᶠ n in atTop, saddleScale f hr.r (HAdmissible.B hf hr) n ≠ 0 := by
    filter_upwards [hrpos, hr.tendsTo.eventually hf.f_pos, hBpos] with n hrn hfn hBn
    exact saddleScale_nonzero_of_pos f hr.r (HAdmissible.B hf hr) n hrn hfn hBn
  filter_upwards [Hsplit, Hnz] with n hsplit hnz
  rw [hsplit]
  dsimp [saddleScale]
  have hS : (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) ≠ 0 := by
    intro hzero
    apply hnz
    simp [hzero, saddleScale]
  have hpref : saddlePref f hr.r n ≠ 0 := by
    intro hpref_zero
    apply hnz
    simp [hpref_zero, saddleScale]
  field_simp [hpref, hS]

private lemma third_central_local_error_isLittleO
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (h2 : SecondOrderHAdmissible hf)
    (h3 : ThirdOrderHAdmissible hf h2)
    (hr : SaddleSequence hf) :
    (fun n : ℕ =>
      (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
          saddleJc f hr.r (HAdmissible.Δ hf hr) n -
        (1 / Real.sqrt (2 * Real.pi) : ℂ) *
          ∫ x in
            -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
              (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
            Complex.exp (-(x ^ 2) / 2) *
              saddleThirdPoly hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) x)
      =o[atTop]
    (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) := by
  let invG : ℂ := (1 / Real.sqrt (2 * Real.pi) : ℂ)
  have hBpos : ∀ᶠ n in atTop, 0 < HAdmissible.B hf hr n := by
    simpa [HAdmissible.B] using hr.tendsTo.eventually hf.b_pos
  have hRpos : ∀ᶠ n in atTop, 0 < hr.r n := by
    simpa using hr.tendsTo.eventually hf.r_pos
  have hδpos : ∀ᶠ n in atTop, 0 < HAdmissible.Δ hf hr n := by
    simpa [HAdmissible.Δ] using hr.tendsTo.eventually hf.δ_pos
  have hdiff :
      ∀ᶠ n in atTop,
        DifferentiableOn ℂ f (Metric.closedBall 0 (hr.r n)) := by
    simpa using hr.tendsTo.eventually hf.differentiableOn
  have hsaddle : ∀ᶠ n in atTop, hf.a (hr.r n) = (n : ℝ) := hr.saddle_eq
  have hCpos : ∀ᶠ n in atTop, 0 < h3.corrScale3 (hr.r n) := by
    simpa using hr.tendsTo.eventually h3.corrScale3_pos
  have hlocalSeq :
      Tendsto
        (fun n : ℕ =>
          (∫ x in
            -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
              (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
            ‖Complex.exp (-(x ^ 2) / 2) *
              (saddleLocalRatio f hf.a hf.b (hr.r n)
                (x / Real.sqrt (HAdmissible.B hf hr n)) -
                saddleThirdPoly hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) x)‖) /
            h3.corrScale3 (hr.r n))
        atTop (𝓝 0) := by
    simpa [HAdmissible.B, HAdmissible.Δ] using h3.local_third_L1.comp hr.tendsTo
  have hupper :
      Tendsto
        (fun n : ℕ =>
          ‖invG‖ *
            ((∫ x in
              -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
              ‖Complex.exp (-(x ^ 2) / 2) *
                (saddleLocalRatio f hf.a hf.b (hr.r n)
                  (x / Real.sqrt (HAdmissible.B hf hr n)) -
                  saddleThirdPoly hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) x)‖) /
              h3.corrScale3 (hr.r n)))
        atTop (𝓝 0) := by
    simpa using hlocalSeq.const_mul ‖invG‖
  have hbound :
      ∀ᶠ n in atTop,
        ‖(Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
              saddleJc f hr.r (HAdmissible.Δ hf hr) n -
            invG *
              ∫ x in
                -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                  (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
                Complex.exp (-(x ^ 2) / 2) *
                  saddleThirdPoly hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) x‖ /
            h3.corrScale3 (hr.r n) ≤
          ‖invG‖ *
            ((∫ x in
              -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
              ‖Complex.exp (-(x ^ 2) / 2) *
                (saddleLocalRatio f hf.a hf.b (hr.r n)
                  (x / Real.sqrt (HAdmissible.B hf hr n)) -
                  saddleThirdPoly hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) x)‖) /
              h3.corrScale3 (hr.r n)) := by
    filter_upwards [hBpos, hRpos, hδpos, hdiff, hsaddle, hCpos] with
      n hBn hRn hδn hdiffn han hCn
    let L : ℝ := HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)
    let G : ℝ → ℂ := fun x => saddleG f hr.r n (x / Real.sqrt (HAdmissible.B hf hr n))
    let P : ℝ → ℂ := fun x =>
      Complex.exp (-(x ^ 2) / 2) *
        saddleThirdPoly hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) x
    let Err : ℝ → ℂ := fun x =>
      Complex.exp (-(x ^ 2) / 2) *
        (saddleLocalRatio f hf.a hf.b (hr.r n)
          (x / Real.sqrt (HAdmissible.B hf hr n)) -
          saddleThirdPoly hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) x)
    have hscaled :
        (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
            saddleJc f hr.r (HAdmissible.Δ hf hr) n =
          invG * ∫ x in -L..L, G x := by
      simpa [L, G, invG] using
        saddleJc_eq_integral_scaled f hr.r (HAdmissible.Δ hf hr)
          (HAdmissible.B hf hr) n hBn
    have hGcont : Continuous G := by
      have h0 := saddleGAt_continuous_of_differentiableOn_closedBall
        f (hr.r n) n hRn.le hdiffn
      have hdiv : Continuous fun x : ℝ => x / Real.sqrt (HAdmissible.B hf hr n) := by
        fun_prop
      simpa [G, saddleG] using h0.comp hdiv
    have hGint : IntervalIntegrable G volume (-L) L :=
      hGcont.intervalIntegrable _ _
    have hPcont : Continuous P := by
      unfold P saddleThirdPoly saddleSecondPoly
      fun_prop
    have hPint : IntervalIntegrable P volume (-L) L :=
      hPcont.intervalIntegrable _ _
    have hsub :
        (∫ x in -L..L, G x) - (∫ x in -L..L, P x) =
          ∫ x in -L..L, G x - P x := by
      rw [intervalIntegral.integral_sub hGint hPint]
    have hErr :
        (fun x : ℝ => G x - P x) = fun x : ℝ => Err x := by
      funext x
      have hGx :
          G x =
            Complex.exp (-(x ^ 2) / 2) *
              saddleLocalRatio f hf.a hf.b (hr.r n)
                (x / Real.sqrt (HAdmissible.B hf hr n)) := by
        simpa [G, saddleG, HAdmissible.B] using
          saddleGAt_eq_gaussian_mul_saddleLocalRatio
            f hf.a hf.b (hr.r n) x n hBn han
      rw [hGx]
      simp [P, Err]
      ring
    have hdiff_eq :
        (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
              saddleJc f hr.r (HAdmissible.Δ hf hr) n -
            invG * (∫ x in -L..L, P x) =
          invG * ∫ x in -L..L, Err x := by
      rw [hscaled]
      rw [← mul_sub]
      rw [hsub]
      rw [hErr]
    have hLnonneg : 0 ≤ L := by
      exact mul_nonneg hδn.le (Real.sqrt_nonneg _)
    have hle : -L ≤ L := by linarith
    have hnormInt :
        ‖∫ x in -L..L, Err x‖ ≤
          ∫ x in -L..L, ‖Err x‖ :=
      intervalIntegral.norm_integral_le_integral_norm hle
    have hnorm :
        ‖(Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
              saddleJc f hr.r (HAdmissible.Δ hf hr) n -
            invG * (∫ x in -L..L, P x)‖ ≤
          ‖invG‖ * (∫ x in -L..L, ‖Err x‖) := by
      rw [hdiff_eq]
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hnormInt (norm_nonneg _)
    have hdiv := div_le_div_of_nonneg_right hnorm hCn.le
    calc
      ‖(Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
            saddleJc f hr.r (HAdmissible.Δ hf hr) n -
          invG * (∫ x in -L..L, P x)‖ / h3.corrScale3 (hr.r n)
          ≤ ‖invG‖ * (∫ x in -L..L, ‖Err x‖) / h3.corrScale3 (hr.r n) := hdiv
      _ = ‖invG‖ *
            ((∫ x in -L..L, ‖Err x‖) / h3.corrScale3 (hr.r n)) := by ring
  have hnonneg :
      ∀ᶠ n in atTop,
        0 ≤
          ‖(Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
                saddleJc f hr.r (HAdmissible.Δ hf hr) n -
              invG *
                ∫ x in
                  -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                    (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
                  Complex.exp (-(x ^ 2) / 2) *
                    saddleThirdPoly hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) x‖ /
              h3.corrScale3 (hr.r n) := by
    filter_upwards [hCpos] with n hCn
    exact div_nonneg (norm_nonneg _) hCn.le
  have hnormdiv :
      Tendsto
        (fun n : ℕ =>
          ‖(Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
                saddleJc f hr.r (HAdmissible.Δ hf hr) n -
              invG *
                ∫ x in
                  -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                    (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
                  Complex.exp (-(x ^ 2) / 2) *
                    saddleThirdPoly hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) x‖ /
              h3.corrScale3 (hr.r n))
        atTop (𝓝 0) :=
    squeeze_zero' hnonneg hbound hupper
  exact complex_isLittleO_of_norm_div_tendsto_zero _ _ hCpos hnormdiv

private lemma gaussian_boundary_exp_div_corr_tendsto_zero
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (h2 : SecondOrderHAdmissible hf)
    (h3 : ThirdOrderHAdmissible hf h2)
    (hr : SaddleSequence hf) :
    Tendsto
      (fun n : ℕ =>
        Real.exp (-(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)) ^ 2 / 2) /
          h3.corrScale3 (hr.r n))
      atTop (𝓝 0) := by
  set_option backward.isDefEq.respectTransparency false in
    rcases h3.tail_third_uniform with ⟨E, hE_nonneg, hdecay, htail⟩
    have hBpos : ∀ᶠ n in atTop, 0 < HAdmissible.B hf hr n := by
      simpa [HAdmissible.B] using hr.tendsTo.eventually hf.b_pos
    have hδpos : ∀ᶠ n in atTop, 0 < HAdmissible.Δ hf hr n := by
      simpa [HAdmissible.Δ] using hr.tendsTo.eventually hf.δ_pos
    have hδπ : ∀ᶠ n in atTop, HAdmissible.Δ hf hr n ≤ Real.pi := by
      simpa [HAdmissible.Δ] using hr.tendsTo.eventually hf.δ_le_pi
    have hsaddle : ∀ᶠ n in atTop, hf.a (hr.r n) = (n : ℝ) := hr.saddle_eq
    have hCpos : ∀ᶠ n in atTop, 0 < h3.corrScale3 (hr.r n) := by
      simpa using hr.tendsTo.eventually h3.corrScale3_pos
    have hE_nonneg_seq : ∀ᶠ n in atTop, 0 ≤ E (hr.r n) := by
      simpa using hr.tendsTo.eventually hE_nonneg
    have htailSeq :
        ∀ᶠ n in atTop, ∀ θ : ℝ,
          HAdmissible.Δ hf hr n ≤ |θ| → |θ| ≤ Real.pi →
            ‖saddleG f hr.r n θ‖ ≤ E (hr.r n) := by
      filter_upwards [hr.tendsTo.eventually htail] with n htailn θ hδθ hθπ
      simpa [HAdmissible.Δ, saddleG] using htailn n θ hδθ hθπ
    have hlocal :
        ∀ᶠ n in atTop, ∀ θ : ℝ,
          |θ| ≤ HAdmissible.Δ hf hr n →
            ‖saddleLocalRatio f hf.a hf.b (hr.r n) θ - 1‖ ≤ (1 / 2 : ℝ) := by
      simpa [HAdmissible.Δ] using
        hr.tendsTo.eventually (hf.local_uniform (1 / 2) (by norm_num))
    have hLtop :
        Tendsto
          (fun n : ℕ => HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))
          atTop atTop := by
      simpa [HAdmissible.B, HAdmissible.Δ] using
        hf.δ_sqrt_b_tendsto_atTop.comp hr.tendsTo
    have hsqrtFactor_ge_one :
        ∀ᶠ n in atTop, 1 ≤ Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) := by
      have hLπ : ∀ᶠ n in atTop,
          Real.pi ≤ HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n) :=
        hLtop.eventually_ge_atTop Real.pi
      filter_upwards [hLπ, hδπ, hBpos] with n hLn hδπn hBn
      have hsqrtB_nonneg : 0 ≤ Real.sqrt (HAdmissible.B hf hr n) := Real.sqrt_nonneg _
      have hπsqrt :
          Real.pi * Real.sqrt (HAdmissible.B hf hr n) ≥ Real.pi := by
        calc
          Real.pi ≤ HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n) := hLn
          _ ≤ Real.pi * Real.sqrt (HAdmissible.B hf hr n) :=
                mul_le_mul_of_nonneg_right hδπn hsqrtB_nonneg
      have hsqrtB_ge_one : 1 ≤ Real.sqrt (HAdmissible.B hf hr n) := by
        have hpi_pos : 0 < Real.pi := Real.pi_pos
        exact (le_mul_iff_one_le_right hpi_pos).mp (by simpa [ge_iff_le] using hπsqrt)
      have hB_ge_one : 1 ≤ HAdmissible.B hf hr n := by
        have hs := Real.sq_sqrt hBn.le
        nlinarith [sq_nonneg (Real.sqrt (HAdmissible.B hf hr n)), hsqrtB_ge_one, hs]
      have harg : 1 ≤ 2 * Real.pi * HAdmissible.B hf hr n := by
        nlinarith [Real.pi_gt_three, hB_ge_one]
      simpa using (Real.one_le_sqrt.mpr harg)
    have hdecaySeq :
        Tendsto
          (fun n : ℕ =>
            Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) * E (hr.r n) /
              h3.corrScale3 (hr.r n))
          atTop (𝓝 0) := by
      simpa [HAdmissible.B] using hdecay.comp hr.tendsTo
    have hupper :
        Tendsto
          (fun n : ℕ =>
            2 * (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) * E (hr.r n) /
              h3.corrScale3 (hr.r n)))
          atTop (𝓝 0) := by
      simpa using hdecaySeq.const_mul 2
    have hbound :
        ∀ᶠ n in atTop,
          Real.exp (-(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)) ^ 2 / 2) /
              h3.corrScale3 (hr.r n) ≤
            2 * (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) * E (hr.r n) /
              h3.corrScale3 (hr.r n)) := by
      filter_upwards [hBpos, hδpos, hδπ, hsaddle, hCpos, hE_nonneg_seq, htailSeq,
        hlocal, hsqrtFactor_ge_one] with
        n hBn hδn hδπn han hCn hEn htailn hlocaln hsqrt_ge_one
      let L : ℝ := HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)
      let θ : ℝ := HAdmissible.Δ hf hr n
      have hsqrt_pos : 0 < Real.sqrt (HAdmissible.B hf hr n) :=
        Real.sqrt_pos.mpr hBn
      have hθeq : L / Real.sqrt (HAdmissible.B hf hr n) = θ := by
        simp [L, θ, div_eq_mul_inv, hsqrt_pos.ne']
      have htheta_abs : |θ| = θ := abs_of_pos hδn
      have hratio_close :
          ‖saddleLocalRatio f hf.a hf.b (hr.r n) θ - 1‖ ≤ (1 / 2 : ℝ) := by
        exact hlocaln θ (by simp [htheta_abs, θ])
      have hratio_lower :
          (1 / 2 : ℝ) ≤
            ‖saddleLocalRatio f hf.a hf.b (hr.r n) θ‖ := by
        have hone :
            ‖(1 : ℂ)‖ ≤
              ‖saddleLocalRatio f hf.a hf.b (hr.r n) θ - 1‖ +
                ‖saddleLocalRatio f hf.a hf.b (hr.r n) θ‖ := by
          calc
            ‖(1 : ℂ)‖ =
                ‖-(saddleLocalRatio f hf.a hf.b (hr.r n) θ - 1) +
                  saddleLocalRatio f hf.a hf.b (hr.r n) θ‖ := by ring_nf
            _ ≤ ‖-(saddleLocalRatio f hf.a hf.b (hr.r n) θ - 1)‖ +
                  ‖saddleLocalRatio f hf.a hf.b (hr.r n) θ‖ :=
                  norm_add_le _ _
            _ = ‖saddleLocalRatio f hf.a hf.b (hr.r n) θ - 1‖ +
                  ‖saddleLocalRatio f hf.a hf.b (hr.r n) θ‖ := by rw [norm_neg]
        norm_num at hone
        linarith
      have hG :
          saddleG f hr.r n θ =
            Complex.exp (-(L ^ 2) / 2) *
              saddleLocalRatio f hf.a hf.b (hr.r n) θ := by
        rw [← hθeq]
        simpa [L, saddleG, HAdmissible.B] using
          saddleGAt_eq_gaussian_mul_saddleLocalRatio
            f hf.a hf.b (hr.r n) L n hBn han
      have hGnorm :
          ‖saddleG f hr.r n θ‖ =
            Real.exp (-(L ^ 2) / 2) *
              ‖saddleLocalRatio f hf.a hf.b (hr.r n) θ‖ := by
        rw [hG, norm_mul]
        have hnormexp :
            ‖Complex.exp (-(L ^ 2) / 2)‖ = Real.exp (-(L ^ 2) / 2) := by
          simp [Complex.norm_exp, sq]
        rw [hnormexp]
      have htail_at : ‖saddleG f hr.r n θ‖ ≤ E (hr.r n) := by
        exact htailn θ (by simp [θ, htheta_abs]) (by simpa [θ, htheta_abs] using hδπn)
      have hexp_nonneg : 0 ≤ Real.exp (-(L ^ 2) / 2) := (Real.exp_pos _).le
      have hexp_le : Real.exp (-(L ^ 2) / 2) ≤ 2 * E (hr.r n) := by
        have hhalf :
            Real.exp (-(L ^ 2) / 2) * (1 / 2 : ℝ) ≤ E (hr.r n) := by
          calc
            Real.exp (-(L ^ 2) / 2) * (1 / 2 : ℝ)
                ≤ Real.exp (-(L ^ 2) / 2) *
                    ‖saddleLocalRatio f hf.a hf.b (hr.r n) θ‖ :=
                      mul_le_mul_of_nonneg_left hratio_lower hexp_nonneg
            _ = ‖saddleG f hr.r n θ‖ := by rw [hGnorm]
            _ ≤ E (hr.r n) := htail_at
        nlinarith
      have hdiv := div_le_div_of_nonneg_right hexp_le hCn.le
      calc
        Real.exp (-(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)) ^ 2 / 2) /
            h3.corrScale3 (hr.r n)
            = Real.exp (-(L ^ 2) / 2) / h3.corrScale3 (hr.r n) := by simp [L]
        _ ≤ 2 * E (hr.r n) / h3.corrScale3 (hr.r n) := hdiv
        _ ≤ 2 * (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) * E (hr.r n) /
              h3.corrScale3 (hr.r n)) := by
            have hEdiv_nonneg : 0 ≤ E (hr.r n) / h3.corrScale3 (hr.r n) :=
              div_nonneg hEn hCn.le
            have hmul :
                E (hr.r n) / h3.corrScale3 (hr.r n) ≤
                  Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) *
                    (E (hr.r n) / h3.corrScale3 (hr.r n)) := by
              simpa using
                mul_le_mul_of_nonneg_right hsqrt_ge_one hEdiv_nonneg
            calc
              2 * E (hr.r n) / h3.corrScale3 (hr.r n)
                  = 2 * (E (hr.r n) / h3.corrScale3 (hr.r n)) := by ring
              _ ≤ 2 * (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) *
                    (E (hr.r n) / h3.corrScale3 (hr.r n))) := by nlinarith
              _ = 2 * (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) *
                    E (hr.r n) / h3.corrScale3 (hr.r n)) := by ring
    have hnonneg :
        ∀ᶠ n in atTop,
          0 ≤
            Real.exp (-(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)) ^ 2 / 2) /
              h3.corrScale3 (hr.r n) := by
      filter_upwards [hCpos] with n hCn
      exact div_nonneg (Real.exp_pos _).le (le_of_lt hCn)
    exact squeeze_zero' hnonneg hbound hupper

private lemma third_window_zero_isLittleO
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (h2 : SecondOrderHAdmissible hf)
    (h3 : ThirdOrderHAdmissible hf h2)
    (hr : SaddleSequence hf) :
    (fun n : ℕ =>
      (1 / Real.sqrt (2 * Real.pi) : ℂ) *
          (∫ x in
            -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
              (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
            Complex.exp (-(x ^ 2) / 2)) -
        1)
      =o[atTop]
    (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) := by
  have hCpos : ∀ᶠ n in atTop, 0 < h3.corrScale3 (hr.r n) := by
    simpa using hr.tendsTo.eventually h3.corrScale3_pos
  have hLtop :
      Tendsto
        (fun n : ℕ => HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))
        atTop atTop := by
    simpa [HAdmissible.B, HAdmissible.Δ] using
      hf.δ_sqrt_b_tendsto_atTop.comp hr.tendsTo
  have hLone :
      ∀ᶠ n in atTop,
        1 ≤ HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n) :=
    hLtop.eventually_ge_atTop 1
  have hboundary := gaussian_boundary_exp_div_corr_tendsto_zero hf h2 h3 hr
  have hupper :
      Tendsto
        (fun n : ℕ =>
          (2 / Real.sqrt (2 * Real.pi)) *
            (Real.exp (-(HAdmissible.Δ hf hr n *
                Real.sqrt (HAdmissible.B hf hr n)) ^ 2 / 2) /
              h3.corrScale3 (hr.r n)))
        atTop (𝓝 0) := by
    simpa using hboundary.const_mul (2 / Real.sqrt (2 * Real.pi))
  have hbound :
      ∀ᶠ n in atTop,
        ‖(1 / Real.sqrt (2 * Real.pi) : ℂ) *
            (∫ x in
              -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
              Complex.exp (-(x ^ 2) / 2)) -
            1‖ / h3.corrScale3 (hr.r n) ≤
          (2 / Real.sqrt (2 * Real.pi)) *
            (Real.exp (-(HAdmissible.Δ hf hr n *
                Real.sqrt (HAdmissible.B hf hr n)) ^ 2 / 2) /
              h3.corrScale3 (hr.r n)) := by
    filter_upwards [hLone, hCpos] with n hLn hCn
    let L : ℝ := HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)
    have hineq := gaussian_window_zero_error_norm_le_exp (L := L) hLn
    have hdiv := div_le_div_of_nonneg_right hineq hCn.le
    calc
      ‖(1 / Real.sqrt (2 * Real.pi) : ℂ) *
          (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2)) - 1‖ /
          h3.corrScale3 (hr.r n)
          ≤ ((2 / Real.sqrt (2 * Real.pi)) * Real.exp (-(L ^ 2) / 2)) /
              h3.corrScale3 (hr.r n) := hdiv
      _ = (2 / Real.sqrt (2 * Real.pi)) *
            (Real.exp (-(L ^ 2) / 2) / h3.corrScale3 (hr.r n)) := by ring
      _ = (2 / Real.sqrt (2 * Real.pi)) *
            (Real.exp (-(HAdmissible.Δ hf hr n *
                Real.sqrt (HAdmissible.B hf hr n)) ^ 2 / 2) /
              h3.corrScale3 (hr.r n)) := by simp [L]
  have hnonneg :
      ∀ᶠ n in atTop,
        0 ≤
          ‖(1 / Real.sqrt (2 * Real.pi) : ℂ) *
              (∫ x in
                -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                  (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
                Complex.exp (-(x ^ 2) / 2)) -
              1‖ / h3.corrScale3 (hr.r n) := by
    filter_upwards [hCpos] with n hCn
    exact div_nonneg (norm_nonneg _) hCn.le
  have hnormdiv :
      Tendsto
        (fun n : ℕ =>
          ‖(1 / Real.sqrt (2 * Real.pi) : ℂ) *
              (∫ x in
                -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                  (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
                Complex.exp (-(x ^ 2) / 2)) -
              1‖ / h3.corrScale3 (hr.r n))
        atTop (𝓝 0) :=
    squeeze_zero' hnonneg hbound hupper
  exact complex_isLittleO_of_norm_div_tendsto_zero _ _ hCpos hnormdiv

private lemma third_window_quartic_isLittleO
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (h2 : SecondOrderHAdmissible hf)
    (h3 : ThirdOrderHAdmissible hf h2)
    (hr : SaddleSequence hf) :
    (fun n : ℕ =>
      (1 / Real.sqrt (2 * Real.pi) : ℂ) *
        (((h2.b4 (hr.r n) : ℂ) /
            (24 * (HAdmissible.B hf hr n : ℂ) ^ 2)) *
          ((∫ x in
              -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
              Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4) -
            (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4))))
      =o[atTop]
    (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) := by
  rcases h3.corrScale3_dominates_correction with ⟨K, hKnonneg, hK⟩
  let L : ℕ → ℝ := fun n =>
    HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)
  let M4 : ℕ → ℂ := fun n =>
    (∫ x in -(L n)..(L n), Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4) -
      (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4)
  let D : ℕ → ℂ := fun n =>
    (h2.b4 (hr.r n) : ℂ) / (24 * (HAdmissible.B hf hr n : ℂ) ^ 2)
  have hBpos : ∀ᶠ n in atTop, 0 < HAdmissible.B hf hr n := by
    simpa [HAdmissible.B] using hr.tendsTo.eventually hf.b_pos
  have hCpos : ∀ᶠ n in atTop, 0 < h3.corrScale3 (hr.r n) := by
    simpa using hr.tendsTo.eventually h3.corrScale3_pos
  have hKseq :
      ∀ᶠ n in atTop,
        saddleThirdCorrectionScale hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) ≤
          K * h3.corrScale3 (hr.r n) := by
    simpa using hr.tendsTo.eventually hK
  have hLtop : Tendsto L atTop atTop := by
    simpa [L, HAdmissible.B, HAdmissible.Δ] using
      hf.δ_sqrt_b_tendsto_atTop.comp hr.tendsTo
  have hM4_tendsto : Tendsto M4 atTop (𝓝 0) := by
    have hwin := gaussian_window_weighted_moment_four_tendsto (L := L) hLtop
    have hconst :
        Tendsto
          (fun _ : ℕ =>
            ∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4)
          atTop
          (𝓝 (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4)) :=
      tendsto_const_nhds
    simpa [M4] using hwin.sub hconst
  have hM4_little : M4 =o[atTop] (fun _ : ℕ => (1 : ℂ)) :=
    (isLittleO_one_iff ℂ).2 hM4_tendsto
  have hD_bigO : D =O[atTop] (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) := by
    refine IsBigO.of_bound ((1 / 24 : ℝ) * K) ?_
    filter_upwards [hBpos, hCpos, hKseq] with n hBn hCn hKn
    have hDle :
        ‖D n‖ ≤ (1 / 24 : ℝ) *
          saddleThirdCorrectionScale hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) := by
      simpa [D, HAdmissible.B] using
        saddleThirdPoly_quarticCoeff_norm_le_scale
          (b := hf.b) (b3 := h2.b3) (b4 := h2.b4) (b5 := h3.b5) (b6 := h3.b6)
          (r := hr.r n) hBn
    calc
      ‖D n‖ ≤ (1 / 24 : ℝ) *
          saddleThirdCorrectionScale hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) := hDle
      _ ≤ (1 / 24 : ℝ) * (K * h3.corrScale3 (hr.r n)) :=
            mul_le_mul_of_nonneg_left hKn (by norm_num)
      _ = ((1 / 24 : ℝ) * K) * ‖(h3.corrScale3 (hr.r n) : ℂ)‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hCn]
            ring
  have hprod := hD_bigO.mul_isLittleO hM4_little
  have hscaled := hprod.const_mul_left (1 / Real.sqrt (2 * Real.pi) : ℂ)
  simpa [D, M4, L, mul_assoc] using hscaled

private lemma third_window_sextic_isLittleO
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (h2 : SecondOrderHAdmissible hf)
    (h3 : ThirdOrderHAdmissible hf h2)
    (hr : SaddleSequence hf) :
    (fun n : ℕ =>
      (1 / Real.sqrt (2 * Real.pi) : ℂ) *
        (((((h2.b3 (hr.r n)) ^ 2 : ℝ) : ℂ) /
            (72 * (HAdmissible.B hf hr n : ℂ) ^ 3)) *
          ((∫ x in
              -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
              Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6) -
            (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6))))
      =o[atTop]
    (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) := by
  rcases h3.corrScale3_dominates_correction with ⟨K, hKnonneg, hK⟩
  let L : ℕ → ℝ := fun n =>
    HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)
  let M6 : ℕ → ℂ := fun n =>
    (∫ x in -(L n)..(L n), Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6) -
      (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)
  let E : ℕ → ℂ := fun n =>
    (((h2.b3 (hr.r n)) ^ 2 : ℝ) : ℂ) /
      (72 * (HAdmissible.B hf hr n : ℂ) ^ 3)
  have hBpos : ∀ᶠ n in atTop, 0 < HAdmissible.B hf hr n := by
    simpa [HAdmissible.B] using hr.tendsTo.eventually hf.b_pos
  have hCpos : ∀ᶠ n in atTop, 0 < h3.corrScale3 (hr.r n) := by
    simpa using hr.tendsTo.eventually h3.corrScale3_pos
  have hKseq :
      ∀ᶠ n in atTop,
        saddleThirdCorrectionScale hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) ≤
          K * h3.corrScale3 (hr.r n) := by
    simpa using hr.tendsTo.eventually hK
  have hLtop : Tendsto L atTop atTop := by
    simpa [L, HAdmissible.B, HAdmissible.Δ] using
      hf.δ_sqrt_b_tendsto_atTop.comp hr.tendsTo
  have hM6_tendsto : Tendsto M6 atTop (𝓝 0) := by
    have hwin := gaussian_window_weighted_moment_six_tendsto (L := L) hLtop
    have hconst :
        Tendsto
          (fun _ : ℕ =>
            ∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)
          atTop
          (𝓝 (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)) :=
      tendsto_const_nhds
    simpa [M6] using hwin.sub hconst
  have hM6_little : M6 =o[atTop] (fun _ : ℕ => (1 : ℂ)) :=
    (isLittleO_one_iff ℂ).2 hM6_tendsto
  have hE_bigO : E =O[atTop] (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) := by
    refine IsBigO.of_bound ((1 / 72 : ℝ) * K) ?_
    filter_upwards [hBpos, hCpos, hKseq] with n hBn hCn hKn
    have hEle :
        ‖E n‖ ≤ (1 / 72 : ℝ) *
          saddleThirdCorrectionScale hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) := by
      simpa [E, HAdmissible.B] using
        saddleThirdPoly_sexticB3Coeff_norm_le_scale
          (b := hf.b) (b3 := h2.b3) (b4 := h2.b4) (b5 := h3.b5) (b6 := h3.b6)
          (r := hr.r n) hBn
    calc
      ‖E n‖ ≤ (1 / 72 : ℝ) *
          saddleThirdCorrectionScale hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) := hEle
      _ ≤ (1 / 72 : ℝ) * (K * h3.corrScale3 (hr.r n)) :=
            mul_le_mul_of_nonneg_left hKn (by norm_num)
      _ = ((1 / 72 : ℝ) * K) * ‖(h3.corrScale3 (hr.r n) : ℂ)‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hCn]
            ring
  have hprod := hE_bigO.mul_isLittleO hM6_little
  have hscaled := hprod.const_mul_left (1 / Real.sqrt (2 * Real.pi) : ℂ)
  simpa [E, M6, L, mul_assoc] using hscaled

private lemma third_window_coeff_moment_isLittleO
    (C M scale : ℕ → ℂ)
    (hC : C =O[atTop] scale)
    (hM : Tendsto M atTop (𝓝 0)) :
    (fun n : ℕ => (1 / Real.sqrt (2 * Real.pi) : ℂ) * (C n * M n))
      =o[atTop] scale := by
  have hM_little : M =o[atTop] (fun _ : ℕ => (1 : ℂ)) :=
    (isLittleO_one_iff ℂ).2 hM
  have hprod := hC.mul_isLittleO hM_little
  simpa [mul_assoc] using
    hprod.const_mul_left (1 / Real.sqrt (2 * Real.pi) : ℂ)

private lemma third_window_b6_isLittleO
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (h2 : SecondOrderHAdmissible hf)
    (h3 : ThirdOrderHAdmissible hf h2)
    (hr : SaddleSequence hf) :
    (fun n : ℕ =>
      (1 / Real.sqrt (2 * Real.pi) : ℂ) *
        (((h3.b6 (hr.r n) : ℂ) /
            (720 * (HAdmissible.B hf hr n : ℂ) ^ 3)) *
          ((∫ x in
              -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
              Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6) -
            (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6))))
      =o[atTop]
    (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) := by
  rcases h3.corrScale3_dominates_correction with ⟨K, hKnonneg, hK⟩
  let L : ℕ → ℝ := fun n =>
    HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)
  let M6 : ℕ → ℂ := fun n =>
    (∫ x in -(L n)..(L n), Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6) -
      (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)
  let C6 : ℕ → ℂ := fun n =>
    (h3.b6 (hr.r n) : ℂ) / (720 * (HAdmissible.B hf hr n : ℂ) ^ 3)
  have hBpos : ∀ᶠ n in atTop, 0 < HAdmissible.B hf hr n := by
    simpa [HAdmissible.B] using hr.tendsTo.eventually hf.b_pos
  have hCpos : ∀ᶠ n in atTop, 0 < h3.corrScale3 (hr.r n) := by
    simpa using hr.tendsTo.eventually h3.corrScale3_pos
  have hKseq :
      ∀ᶠ n in atTop,
        saddleThirdCorrectionScale hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) ≤
          K * h3.corrScale3 (hr.r n) := by
    simpa using hr.tendsTo.eventually hK
  have hLtop : Tendsto L atTop atTop := by
    simpa [L, HAdmissible.B, HAdmissible.Δ] using
      hf.δ_sqrt_b_tendsto_atTop.comp hr.tendsTo
  have hM6_tendsto : Tendsto M6 atTop (𝓝 0) := by
    have hwin := gaussian_window_weighted_moment_six_tendsto (L := L) hLtop
    have hconst :
        Tendsto
          (fun _ : ℕ =>
            ∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)
          atTop
          (𝓝 (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6)) :=
      tendsto_const_nhds
    simpa [M6] using hwin.sub hconst
  have hC_bigO : C6 =O[atTop] (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) := by
    refine IsBigO.of_bound ((1 / 720 : ℝ) * K) ?_
    filter_upwards [hBpos, hCpos, hKseq] with n hBn hCn hKn
    have hCle :
        ‖C6 n‖ ≤ (1 / 720 : ℝ) *
          saddleThirdCorrectionScale hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) := by
      simpa [C6, HAdmissible.B] using
        saddleThirdPoly_b6Coeff_norm_le_scale
          (b := hf.b) (b3 := h2.b3) (b4 := h2.b4) (b5 := h3.b5) (b6 := h3.b6)
          (r := hr.r n) hBn
    calc
      ‖C6 n‖ ≤ (1 / 720 : ℝ) *
          saddleThirdCorrectionScale hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) := hCle
      _ ≤ (1 / 720 : ℝ) * (K * h3.corrScale3 (hr.r n)) :=
            mul_le_mul_of_nonneg_left hKn (by norm_num)
      _ = ((1 / 720 : ℝ) * K) * ‖(h3.corrScale3 (hr.r n) : ℂ)‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hCn]
            ring
  exact third_window_coeff_moment_isLittleO C6 M6
    (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) hC_bigO hM6_tendsto

private lemma third_window_b3b5_isLittleO
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (h2 : SecondOrderHAdmissible hf)
    (h3 : ThirdOrderHAdmissible hf h2)
    (hr : SaddleSequence hf) :
    (fun n : ℕ =>
      (1 / Real.sqrt (2 * Real.pi) : ℂ) *
        ((((h2.b3 (hr.r n) * h3.b5 (hr.r n) : ℝ) : ℂ) /
            (720 * (HAdmissible.B hf hr n : ℂ) ^ 4)) *
          ((∫ x in
              -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
              Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8) -
            (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8))))
      =o[atTop]
    (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) := by
  rcases h3.corrScale3_dominates_correction with ⟨K, hKnonneg, hK⟩
  let L : ℕ → ℝ := fun n =>
    HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)
  let M8 : ℕ → ℂ := fun n =>
    (∫ x in -(L n)..(L n), Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8) -
      (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8)
  let C8 : ℕ → ℂ := fun n =>
    (((h2.b3 (hr.r n) * h3.b5 (hr.r n) : ℝ) : ℂ) /
      (720 * (HAdmissible.B hf hr n : ℂ) ^ 4))
  have hBpos : ∀ᶠ n in atTop, 0 < HAdmissible.B hf hr n := by
    simpa [HAdmissible.B] using hr.tendsTo.eventually hf.b_pos
  have hCpos : ∀ᶠ n in atTop, 0 < h3.corrScale3 (hr.r n) := by
    simpa using hr.tendsTo.eventually h3.corrScale3_pos
  have hKseq :
      ∀ᶠ n in atTop,
        saddleThirdCorrectionScale hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) ≤
          K * h3.corrScale3 (hr.r n) := by
    simpa using hr.tendsTo.eventually hK
  have hLtop : Tendsto L atTop atTop := by
    simpa [L, HAdmissible.B, HAdmissible.Δ] using
      hf.δ_sqrt_b_tendsto_atTop.comp hr.tendsTo
  have hM8_tendsto : Tendsto M8 atTop (𝓝 0) := by
    have hwin := gaussian_window_weighted_moment_eight_tendsto (L := L) hLtop
    have hconst :
        Tendsto
          (fun _ : ℕ =>
            ∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8)
          atTop
          (𝓝 (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8)) :=
      tendsto_const_nhds
    simpa [M8] using hwin.sub hconst
  have hC_bigO : C8 =O[atTop] (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) := by
    refine IsBigO.of_bound ((1 / 720 : ℝ) * K) ?_
    filter_upwards [hBpos, hCpos, hKseq] with n hBn hCn hKn
    have hCle :
        ‖C8 n‖ ≤ (1 / 720 : ℝ) *
          saddleThirdCorrectionScale hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) := by
      simpa [C8, HAdmissible.B] using
        saddleThirdPoly_b3b5Coeff_norm_le_scale
          (b := hf.b) (b3 := h2.b3) (b4 := h2.b4) (b5 := h3.b5) (b6 := h3.b6)
          (r := hr.r n) hBn
    calc
      ‖C8 n‖ ≤ (1 / 720 : ℝ) *
          saddleThirdCorrectionScale hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) := hCle
      _ ≤ (1 / 720 : ℝ) * (K * h3.corrScale3 (hr.r n)) :=
            mul_le_mul_of_nonneg_left hKn (by norm_num)
      _ = ((1 / 720 : ℝ) * K) * ‖(h3.corrScale3 (hr.r n) : ℂ)‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hCn]
            ring
  exact third_window_coeff_moment_isLittleO C8 M8
    (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) hC_bigO hM8_tendsto

private lemma third_window_b4sq_isLittleO
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (h2 : SecondOrderHAdmissible hf)
    (h3 : ThirdOrderHAdmissible hf h2)
    (hr : SaddleSequence hf) :
    (fun n : ℕ =>
      (1 / Real.sqrt (2 * Real.pi) : ℂ) *
        (((((h2.b4 (hr.r n)) ^ 2 : ℝ) : ℂ) /
            (1152 * (HAdmissible.B hf hr n : ℂ) ^ 4)) *
          ((∫ x in
              -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
              Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8) -
            (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8))))
      =o[atTop]
    (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) := by
  rcases h3.corrScale3_dominates_correction with ⟨K, hKnonneg, hK⟩
  let L : ℕ → ℝ := fun n =>
    HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)
  let M8 : ℕ → ℂ := fun n =>
    (∫ x in -(L n)..(L n), Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8) -
      (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8)
  let C8 : ℕ → ℂ := fun n =>
    ((((h2.b4 (hr.r n)) ^ 2 : ℝ) : ℂ) /
      (1152 * (HAdmissible.B hf hr n : ℂ) ^ 4))
  have hBpos : ∀ᶠ n in atTop, 0 < HAdmissible.B hf hr n := by
    simpa [HAdmissible.B] using hr.tendsTo.eventually hf.b_pos
  have hCpos : ∀ᶠ n in atTop, 0 < h3.corrScale3 (hr.r n) := by
    simpa using hr.tendsTo.eventually h3.corrScale3_pos
  have hKseq :
      ∀ᶠ n in atTop,
        saddleThirdCorrectionScale hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) ≤
          K * h3.corrScale3 (hr.r n) := by
    simpa using hr.tendsTo.eventually hK
  have hLtop : Tendsto L atTop atTop := by
    simpa [L, HAdmissible.B, HAdmissible.Δ] using
      hf.δ_sqrt_b_tendsto_atTop.comp hr.tendsTo
  have hM8_tendsto : Tendsto M8 atTop (𝓝 0) := by
    have hwin := gaussian_window_weighted_moment_eight_tendsto (L := L) hLtop
    have hconst :
        Tendsto
          (fun _ : ℕ =>
            ∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8)
          atTop
          (𝓝 (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8)) :=
      tendsto_const_nhds
    simpa [M8] using hwin.sub hconst
  have hC_bigO : C8 =O[atTop] (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) := by
    refine IsBigO.of_bound ((1 / 1152 : ℝ) * K) ?_
    filter_upwards [hBpos, hCpos, hKseq] with n hBn hCn hKn
    have hCle :
        ‖C8 n‖ ≤ (1 / 1152 : ℝ) *
          saddleThirdCorrectionScale hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) := by
      simpa [C8, HAdmissible.B] using
        saddleThirdPoly_b4sqCoeff_norm_le_scale
          (b := hf.b) (b3 := h2.b3) (b4 := h2.b4) (b5 := h3.b5) (b6 := h3.b6)
          (r := hr.r n) hBn
    calc
      ‖C8 n‖ ≤ (1 / 1152 : ℝ) *
          saddleThirdCorrectionScale hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) := hCle
      _ ≤ (1 / 1152 : ℝ) * (K * h3.corrScale3 (hr.r n)) :=
            mul_le_mul_of_nonneg_left hKn (by norm_num)
      _ = ((1 / 1152 : ℝ) * K) * ‖(h3.corrScale3 (hr.r n) : ℂ)‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hCn]
            ring
  exact third_window_coeff_moment_isLittleO C8 M8
    (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) hC_bigO hM8_tendsto

private lemma third_window_b3sqb4_isLittleO
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (h2 : SecondOrderHAdmissible hf)
    (h3 : ThirdOrderHAdmissible hf h2)
    (hr : SaddleSequence hf) :
    (fun n : ℕ =>
      (1 / Real.sqrt (2 * Real.pi) : ℂ) *
        (((((h2.b3 (hr.r n)) ^ 2 * h2.b4 (hr.r n) : ℝ) : ℂ) /
            (1728 * (HAdmissible.B hf hr n : ℂ) ^ 5)) *
          ((∫ x in
              -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
              Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 10) -
            (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 10))))
      =o[atTop]
    (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) := by
  rcases h3.corrScale3_dominates_correction with ⟨K, hKnonneg, hK⟩
  let L : ℕ → ℝ := fun n =>
    HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)
  let M10 : ℕ → ℂ := fun n =>
    (∫ x in -(L n)..(L n), Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 10) -
      (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 10)
  let C10 : ℕ → ℂ := fun n =>
    ((((h2.b3 (hr.r n)) ^ 2 * h2.b4 (hr.r n) : ℝ) : ℂ) /
      (1728 * (HAdmissible.B hf hr n : ℂ) ^ 5))
  have hBpos : ∀ᶠ n in atTop, 0 < HAdmissible.B hf hr n := by
    simpa [HAdmissible.B] using hr.tendsTo.eventually hf.b_pos
  have hCpos : ∀ᶠ n in atTop, 0 < h3.corrScale3 (hr.r n) := by
    simpa using hr.tendsTo.eventually h3.corrScale3_pos
  have hKseq :
      ∀ᶠ n in atTop,
        saddleThirdCorrectionScale hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) ≤
          K * h3.corrScale3 (hr.r n) := by
    simpa using hr.tendsTo.eventually hK
  have hLtop : Tendsto L atTop atTop := by
    simpa [L, HAdmissible.B, HAdmissible.Δ] using
      hf.δ_sqrt_b_tendsto_atTop.comp hr.tendsTo
  have hM10_tendsto : Tendsto M10 atTop (𝓝 0) := by
    have hwin := gaussian_window_weighted_moment_ten_tendsto (L := L) hLtop
    have hconst :
        Tendsto
          (fun _ : ℕ =>
            ∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 10)
          atTop
          (𝓝 (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 10)) :=
      tendsto_const_nhds
    simpa [M10] using hwin.sub hconst
  have hC_bigO : C10 =O[atTop] (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) := by
    refine IsBigO.of_bound ((1 / 1728 : ℝ) * K) ?_
    filter_upwards [hBpos, hCpos, hKseq] with n hBn hCn hKn
    have hCle :
        ‖C10 n‖ ≤ (1 / 1728 : ℝ) *
          saddleThirdCorrectionScale hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) := by
      simpa [C10, HAdmissible.B] using
        saddleThirdPoly_b3sqb4Coeff_norm_le_scale
          (b := hf.b) (b3 := h2.b3) (b4 := h2.b4) (b5 := h3.b5) (b6 := h3.b6)
          (r := hr.r n) hBn
    calc
      ‖C10 n‖ ≤ (1 / 1728 : ℝ) *
          saddleThirdCorrectionScale hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) := hCle
      _ ≤ (1 / 1728 : ℝ) * (K * h3.corrScale3 (hr.r n)) :=
            mul_le_mul_of_nonneg_left hKn (by norm_num)
      _ = ((1 / 1728 : ℝ) * K) * ‖(h3.corrScale3 (hr.r n) : ℂ)‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hCn]
            ring
  exact third_window_coeff_moment_isLittleO C10 M10
    (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) hC_bigO hM10_tendsto

private lemma third_window_b3four_isLittleO
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (h2 : SecondOrderHAdmissible hf)
    (h3 : ThirdOrderHAdmissible hf h2)
    (hr : SaddleSequence hf) :
    (fun n : ℕ =>
      (1 / Real.sqrt (2 * Real.pi) : ℂ) *
        (((((h2.b3 (hr.r n)) ^ 4 : ℝ) : ℂ) /
            (31104 * (HAdmissible.B hf hr n : ℂ) ^ 6)) *
          ((∫ x in
              -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
              Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 12) -
            (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 12))))
      =o[atTop]
    (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) := by
  rcases h3.corrScale3_dominates_correction with ⟨K, hKnonneg, hK⟩
  let L : ℕ → ℝ := fun n =>
    HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)
  let M12 : ℕ → ℂ := fun n =>
    (∫ x in -(L n)..(L n), Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 12) -
      (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 12)
  let C12 : ℕ → ℂ := fun n =>
    ((((h2.b3 (hr.r n)) ^ 4 : ℝ) : ℂ) /
      (31104 * (HAdmissible.B hf hr n : ℂ) ^ 6))
  have hBpos : ∀ᶠ n in atTop, 0 < HAdmissible.B hf hr n := by
    simpa [HAdmissible.B] using hr.tendsTo.eventually hf.b_pos
  have hCpos : ∀ᶠ n in atTop, 0 < h3.corrScale3 (hr.r n) := by
    simpa using hr.tendsTo.eventually h3.corrScale3_pos
  have hKseq :
      ∀ᶠ n in atTop,
        saddleThirdCorrectionScale hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) ≤
          K * h3.corrScale3 (hr.r n) := by
    simpa using hr.tendsTo.eventually hK
  have hLtop : Tendsto L atTop atTop := by
    simpa [L, HAdmissible.B, HAdmissible.Δ] using
      hf.δ_sqrt_b_tendsto_atTop.comp hr.tendsTo
  have hM12_tendsto : Tendsto M12 atTop (𝓝 0) := by
    have hwin := gaussian_window_weighted_moment_twelve_tendsto (L := L) hLtop
    have hconst :
        Tendsto
          (fun _ : ℕ =>
            ∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 12)
          atTop
          (𝓝 (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 12)) :=
      tendsto_const_nhds
    simpa [M12] using hwin.sub hconst
  have hC_bigO : C12 =O[atTop] (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) := by
    refine IsBigO.of_bound ((1 / 31104 : ℝ) * K) ?_
    filter_upwards [hBpos, hCpos, hKseq] with n hBn hCn hKn
    have hCle :
        ‖C12 n‖ ≤ (1 / 31104 : ℝ) *
          saddleThirdCorrectionScale hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) := by
      simpa [C12, HAdmissible.B] using
        saddleThirdPoly_b3fourCoeff_norm_le_scale
          (b := hf.b) (b3 := h2.b3) (b4 := h2.b4) (b5 := h3.b5) (b6 := h3.b6)
          (r := hr.r n) hBn
    calc
      ‖C12 n‖ ≤ (1 / 31104 : ℝ) *
          saddleThirdCorrectionScale hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) := hCle
      _ ≤ (1 / 31104 : ℝ) * (K * h3.corrScale3 (hr.r n)) :=
            mul_le_mul_of_nonneg_left hKn (by norm_num)
      _ = ((1 / 31104 : ℝ) * K) * ‖(h3.corrScale3 (hr.r n) : ℂ)‖ := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hCn]
            ring
  exact third_window_coeff_moment_isLittleO C12 M12
    (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) hC_bigO hM12_tendsto

private lemma third_window_poly_integral_isLittleO
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (h2 : SecondOrderHAdmissible hf)
    (h3 : ThirdOrderHAdmissible hf h2)
    (hr : SaddleSequence hf) :
    (fun n : ℕ =>
      (1 / Real.sqrt (2 * Real.pi) : ℂ) *
          (∫ x in
            -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
              (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
            Complex.exp (-(x ^ 2) / 2) *
              saddleThirdPoly hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) x) -
        (1 + (saddleCorrection hf.b h2.b3 h2.b4 (hr.r n) : ℂ) +
          (saddleThirdCorrection hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) : ℂ)))
      =o[atTop]
    (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) := by
  have h0 := third_window_zero_isLittleO hf h2 h3 hr
  have h4 := third_window_quartic_isLittleO hf h2 h3 hr
  have h6 := third_window_sextic_isLittleO hf h2 h3 hr
  have h6b := third_window_b6_isLittleO hf h2 h3 hr
  have h8a := third_window_b3b5_isLittleO hf h2 h3 hr
  have h8b := third_window_b4sq_isLittleO hf h2 h3 hr
  have h10 := third_window_b3sqb4_isLittleO hf h2 h3 hr
  have h12 := third_window_b3four_isLittleO hf h2 h3 hr
  have hsum := (((h0.add ((h4.sub h6).sub h6b)).add h8a).add h8b).sub h10 |>.add h12
  refine hsum.congr_left ?_
  intro n
  let L : ℝ := HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)
  let invG : ℂ := (1 / Real.sqrt (2 * Real.pi) : ℂ)
  let W0 : ℂ := ∫ x in -L..L, Complex.exp (-(x ^ 2) / 2)
  let W4 : ℂ := ∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4
  let W6 : ℂ := ∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6
  let W8 : ℂ := ∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8
  let W10 : ℂ := ∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 10
  let W12 : ℂ := ∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 12
  let F4 : ℂ := ∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 4
  let F6 : ℂ := ∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 6
  let F8 : ℂ := ∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 8
  let F10 : ℂ := ∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 10
  let F12 : ℂ := ∫ x : ℝ, Complex.exp (-(x ^ 2) / 2) * (x : ℂ) ^ 12
  let D : ℂ := (h2.b4 (hr.r n) : ℂ) / (24 * (HAdmissible.B hf hr n : ℂ) ^ 2)
  let E : ℂ := (((h2.b3 (hr.r n)) ^ 2 : ℝ) : ℂ) /
    (72 * (HAdmissible.B hf hr n : ℂ) ^ 3)
  let C6 : ℂ := (h3.b6 (hr.r n) : ℂ) / (720 * (HAdmissible.B hf hr n : ℂ) ^ 3)
  let C8a : ℂ := (((h2.b3 (hr.r n) * h3.b5 (hr.r n) : ℝ) : ℂ) /
    (720 * (HAdmissible.B hf hr n : ℂ) ^ 4))
  let C8b : ℂ := ((((h2.b4 (hr.r n)) ^ 2 : ℝ) : ℂ) /
    (1152 * (HAdmissible.B hf hr n : ℂ) ^ 4))
  let C10 : ℂ := (((h2.b3 (hr.r n)) ^ 2 * h2.b4 (hr.r n) : ℝ) : ℂ) /
    (1728 * (HAdmissible.B hf hr n : ℂ) ^ 5)
  let C12 : ℂ := (((h2.b3 (hr.r n)) ^ 4 : ℝ) : ℂ) /
    (31104 * (HAdmissible.B hf hr n : ℂ) ^ 6)
  have hwin :
      (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) *
          saddleThirdPoly hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) x) =
        W0 + D * W4 - E * W6 - C6 * W6 + C8a * W8 + C8b * W8 -
          C10 * W10 + C12 * W12 := by
    simpa [L, W0, W4, W6, W8, W10, W12, D, E, C6, C8a, C8b, C10, C12,
      HAdmissible.B] using
      gaussian_window_integral_saddleThirdPoly
        hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) L
  have hcorr1 :
      (saddleCorrection hf.b h2.b3 h2.b4 (hr.r n) : ℂ) =
        invG * (D * F4 - E * F6) := by
    simpa [invG, D, E, F4, F6, HAdmissible.B] using
      saddleCorrection_eq_gaussian_even_moments
        hf.b h2.b3 h2.b4 (hr.r n)
  have hcorr2 :
      (saddleThirdCorrection hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) : ℂ) =
        invG * (-C6 * F6 + C8a * F8 + C8b * F8 - C10 * F10 + C12 * F12) := by
    simpa [invG, C6, C8a, C8b, C10, C12, F6, F8, F10, F12, HAdmissible.B] using
      saddleThirdCorrection_eq_gaussian_even_moments
        hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n)
  calc
    (((((invG * W0 - 1) +
          ((invG * (D * (W4 - F4)) - invG * (E * (W6 - F6))) -
            invG * (C6 * (W6 - F6)))) +
          invG * (C8a * (W8 - F8))) +
          invG * (C8b * (W8 - F8))) -
          invG * (C10 * (W10 - F10))) +
          invG * (C12 * (W12 - F12))
        = invG * (W0 + D * W4 - E * W6 - C6 * W6 + C8a * W8 + C8b * W8 -
            C10 * W10 + C12 * W12) -
            (1 + (saddleCorrection hf.b h2.b3 h2.b4 (hr.r n) : ℂ) +
              (saddleThirdCorrection hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) : ℂ)) := by
          rw [hcorr1, hcorr2]
          ring
    _ = invG *
          (∫ x in -L..L, Complex.exp (-(x ^ 2) / 2) *
            saddleThirdPoly hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) x) -
          (1 + (saddleCorrection hf.b h2.b3 h2.b4 (hr.r n) : ℂ) +
            (saddleThirdCorrection hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) : ℂ)) := by
          rw [hwin]
    _ =
        (1 / Real.sqrt (2 * Real.pi) : ℂ) *
            (∫ x in
              -(HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))..
                (HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n)),
              Complex.exp (-(x ^ 2) / 2) *
                saddleThirdPoly hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) x) -
          (1 + (saddleCorrection hf.b h2.b3 h2.b4 (hr.r n) : ℂ) +
            (saddleThirdCorrection hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) : ℂ)) := by
          simp [L, invG]

/-- Abstract third-order saddle ratio theorem. -/
theorem coeff_thirdOrder_saddle
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (h2 : SecondOrderHAdmissible hf)
    (h3 : ThirdOrderHAdmissible hf h2)
    (hr : SaddleSequence hf) :
    (fun n : ℕ =>
      p.coeff n / saddleScale f hr.r (HAdmissible.B hf hr) n -
        (1 + (saddleCorrection hf.b h2.b3 h2.b4 (hr.r n) : ℂ) +
          (saddleThirdCorrection hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) : ℂ)))
      =o[atTop]
    (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) :=
  by
    have hcentral := third_central_local_error_isLittleO hf h2 h3 hr
    have hpoly := third_window_poly_integral_isLittleO hf h2 h3 hr
    have htail := third_tail_isLittleO hf h2 h3 hr
    have hcentralCorr :
        (fun n : ℕ =>
          (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
              saddleJc f hr.r (HAdmissible.Δ hf hr) n -
            (1 + (saddleCorrection hf.b h2.b3 h2.b4 (hr.r n) : ℂ) +
              (saddleThirdCorrection hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) : ℂ)))
          =o[atTop]
        (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) := by
      have h := hcentral.add hpoly
      refine h.congr_left ?_
      intro n
      ring
    have hscaled :
        (fun n : ℕ =>
          (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
              (saddleJc f hr.r (HAdmissible.Δ hf hr) n +
                saddleJt f hr.r (HAdmissible.Δ hf hr) n) -
            (1 + (saddleCorrection hf.b h2.b3 h2.b4 (hr.r n) : ℂ) +
              (saddleThirdCorrection hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) : ℂ)))
          =o[atTop]
        (fun n : ℕ => (h3.corrScale3 (hr.r n) : ℂ)) := by
      have h := hcentralCorr.add htail
      refine h.congr_left ?_
      intro n
      ring
    have hratio := coeff_ratio_eq_scaled_saddleJ_eventually hf hr
    have htarget :
        (fun n : ℕ =>
          p.coeff n / saddleScale f hr.r (HAdmissible.B hf hr) n -
            (1 + (saddleCorrection hf.b h2.b3 h2.b4 (hr.r n) : ℂ) +
              (saddleThirdCorrection hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) : ℂ)))
          =ᶠ[atTop]
        (fun n : ℕ =>
          (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
              (saddleJc f hr.r (HAdmissible.Δ hf hr) n +
                saddleJt f hr.r (HAdmissible.Δ hf hr) n) -
            (1 + (saddleCorrection hf.b h2.b3 h2.b4 (hr.r n) : ℂ) +
              (saddleThirdCorrection hf.b h2.b3 h2.b4 h3.b5 h3.b6 (hr.r n) : ℂ))) := by
      filter_upwards [hratio] with n hn
      rw [hn]
    exact htarget.trans_isLittleO hscaled

end

/-!
# Third-order saddle data for Bell numbers

This file instantiates the third-order Hayman wrapper for
`exp (exp z - 1)`.  The fifth and sixth logarithmic saddle derivatives are
the next two Touchard polynomials evaluated at the Bell saddle.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

set_option maxHeartbeats 1400000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

noncomputable section

theorem bell_coeff_thirdOrder_saddle_from_HAdmissible :
    (fun n : ℕ =>
      bellSeries.coeff n / bellSecondOrderSaddleScale n -
        (1 + (saddleCorrection bellSaddleBReal bellSaddleB3Real bellSaddleB4Real
          (bellSaddleRadius n) : ℂ) +
          (saddleThirdCorrection bellSaddleBReal bellSaddleB3Real bellSaddleB4Real
            bellSaddleB5Real bellSaddleB6Real (bellSaddleRadius n) : ℂ)))
      =o[atTop]
    (fun n : ℕ => (bellThirdCorrScale (bellSaddleRadius n) : ℂ)) := by
  have h :=
    coeff_thirdOrder_saddle
      bellHAdmissible bellSecondOrderHAdmissible bellThirdOrderHAdmissible
      bellHAdmissibleSaddleSequence
  simpa [bellSecondOrderSaddleScale, HAdmissible.B, bellHAdmissible,
    bellHAdmissibleSaddleSequence, bellSecondOrderHAdmissible, bellThirdCorrScale] using h

theorem bellCarrier_coeff_thirdOrder_saddle_from_HAdmissible :
    (fun n : ℕ =>
      (PowerSeries.toFMLS bellCarrier).coeff n / bellSecondOrderSaddleScale n -
        (1 + (saddleCorrection bellSaddleBReal bellSaddleB3Real bellSaddleB4Real
          (bellSaddleRadius n) : ℂ) +
          (saddleThirdCorrection bellSaddleBReal bellSaddleB3Real bellSaddleB4Real
            bellSaddleB5Real bellSaddleB6Real (bellSaddleRadius n) : ℂ)))
      =o[atTop]
    (fun n : ℕ => (bellThirdCorrScale (bellSaddleRadius n) : ℂ)) := by
  simpa [bellSeries, bellCarrier_toFMLS_eq_analyticBellSeries] using
    bell_coeff_thirdOrder_saddle_from_HAdmissible

end

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries
set_option maxHeartbeats 1400000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
theorem solution :
    (fun n : ℕ =>
      (((AnalyticCombinatorics.Ch1.CombClass.posInt.set.counts n : ℝ) /
          n.factorial : ℝ) : ℂ) / bellSecondOrderSaddleScale n -
        (1 + (saddleCorrection bellSaddleBReal bellSaddleB3Real bellSaddleB4Real
          (bellSaddleRadius n) : ℂ) +
          (saddleThirdCorrection bellSaddleBReal bellSaddleB3Real bellSaddleB4Real
            bellSaddleB5Real bellSaddleB6Real (bellSaddleRadius n) : ℂ)))
      =o[atTop]
    (fun n : ℕ => (bellThirdCorrScale (bellSaddleRadius n) : ℂ)) := by
  simpa [bellSecondOrderSaddleScale, PowerSeries.coeff_toFMLS, bellCarrier_coeff,
    bellCoeffR] using bellCarrier_coeff_thirdOrder_saddle_from_HAdmissible
