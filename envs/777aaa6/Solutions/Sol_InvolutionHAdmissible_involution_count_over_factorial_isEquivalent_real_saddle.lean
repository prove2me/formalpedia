-- Prove2me | solution 1 for InvolutionHAdmissible.involution_count_over_factorial_isEquivalent_real_saddle
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-27T23:04:20.767545+00:00
-- url     : https://prove2.me/submissions/45666b1f-a095-4dc1-88cc-3cc80340f7aa

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Bridge
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Poles
import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_SubstComp
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Assembly
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Bound
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ExpStirling
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_GaussianMoments
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_SecondOrderCore
import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Fibonacci
import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Sequence
import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_SequenceInverse
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_Defs
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledProduct
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSet
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Exp
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_GaussianCore
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_HAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ThirdOrderCore
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledPower
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSetOde
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_Bell
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ExpHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_SecondOrderHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_InvolutionHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledSeq
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_BellHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_ThirdOrderHAdmissible
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_InvolutionRealSaddle
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_InvolutionSecondOrder
import Definitions.Def_AnalyticCombinatorics_Ch8_SaddlePoint_InvolutionThirdOrder
import Mathlib
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Analytic.Composition
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Order.Partition.Finpartition
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Fintype.EquivFin
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Ch1 §I.3 — Fibonacci numbers as compositions into parts `1` and `2`

Flajolet & Sedgewick, Part A, Chapter I, §I.3. Let `D` be the class with one
object of size `1` and one of size `2`. Then `SEQ(D)` enumerates compositions of
`n` into parts of size `1` and `2`, and

* `counts_seq_parts12` — there are `F_{n+1}` of them (`Nat.fib (n+1)`), via the
  convolution recursion `counts_seq_succ`, which here is the Fibonacci recurrence;
* `ogf_parts12` / `ogf_seq_parts12` — `D(z) = z + z²` and the OGF is
  `1/(1 - z - z²)`, the Fibonacci generating function.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

@[simp] lemma CombClass.counts_parts12 (n : ℕ) :
    CombClass.parts12.counts n = if n = 1 then 1 else if n = 2 then 1 else 0 :=
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

/-- The EGF of the "singletons-and-pairs" class is `z + z²/2`. -/
theorem CombClass.egf_parts12_egf :
    CombClass.parts12.egf = X + (2⁻¹ : ℚ) • X ^ 2 := by
  ext n
  rw [CombClass.coeff_egf, CombClass.counts_parts12, map_add, coeff_X, map_smul, coeff_X_pow,
    smul_eq_mul]
  rcases n with _ | _ | _ | m <;> norm_num [Nat.factorial] <;> omega

/-- **Involutions** (F&S §II.3): an involution is a set of fixed points and
transpositions, `SET(ℙ₁₂)` where `ℙ₁₂` has one object each of size 1 and 2.
Its EGF is `exp(z + z²/2)`. -/
theorem CombClass.egf_involutions :
    CombClass.parts12.set.egf = (PowerSeries.exp ℚ).subst (X + (2⁻¹ : ℚ) • X ^ 2) := by
  rw [CombClass.egf_set _ (by simp [CombClass.counts_parts12]), CombClass.egf_parts12_egf]

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

/-!
# Real-valued central-binomial and Catalan asymptotics

This file reflects the complex-valued asymptotic equivalents back to their
natural real-valued forms.
-/

open Filter Asymptotics
open scoped Topology BigOperators

lemma ofReal_isEquivalent_iff {f g : ℕ → ℝ} :
    ((fun n => (f n : ℂ)) ~[atTop] (fun n => (g n : ℂ))) ↔
      f ~[atTop] g := by
  constructor
  · intro h
    rw [Asymptotics.IsEquivalent] at h ⊢
    rw [Asymptotics.isLittleO_iff] at h ⊢
    intro c hc
    specialize h hc
    filter_upwards [h] with n hn
    simpa [Pi.sub_apply, ← Complex.ofReal_sub, Complex.norm_real] using hn
  · intro h
    rw [Asymptotics.IsEquivalent] at h ⊢
    rw [Asymptotics.isLittleO_iff] at h ⊢
    intro c hc
    specialize h hc
    filter_upwards [h] with n hn
    simpa [Pi.sub_apply, ← Complex.ofReal_sub, Complex.norm_real] using hn

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

/-- Assembly theorem from an exact central/tail split and normalized limits. -/
theorem coeff_isEquivalent_saddle_assembly
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} (r B δ : ℕ → ℝ)
    (Hsplit : ∀ᶠ n in atTop,
      p.coeff n = saddlePref f r n * (saddleJc f r δ n + saddleJt f r δ n))
    (Hcentral : Tendsto
      (fun n : ℕ => (Real.sqrt (2 * Real.pi * B n) : ℂ) * saddleJc f r δ n)
      atTop (𝓝 1))
    (Htail : Tendsto
      (fun n : ℕ => (Real.sqrt (2 * Real.pi * B n) : ℂ) * saddleJt f r δ n)
      atTop (𝓝 0))
    (Hnz : ∀ᶠ n in atTop, saddleScale f r B n ≠ 0) :
    (fun n : ℕ => p.coeff n) ~[atTop] (fun n : ℕ => saddleScale f r B n) := by
  apply Asymptotics.isEquivalent_of_tendsto_one
  let S : ℕ → ℂ := fun n => (Real.sqrt (2 * Real.pi * B n) : ℂ)
  have hratio :
      (fun n : ℕ => p.coeff n / saddleScale f r B n) =ᶠ[atTop]
        (fun n : ℕ => S n * (saddleJc f r δ n + saddleJt f r δ n)) := by
    filter_upwards [Hsplit, Hnz] with n hsplit hnz
    rw [hsplit]
    dsimp [S, saddleScale]
    have hS : (Real.sqrt (2 * Real.pi * B n) : ℂ) ≠ 0 := by
      intro hzero
      apply hnz
      simp [hzero, saddleScale]
    have hpref : saddlePref f r n ≠ 0 := by
      intro hpref_zero
      apply hnz
      simp [hpref_zero, saddleScale]
    field_simp [hpref, hS]
  have hsum :
      Tendsto (fun n : ℕ => S n * (saddleJc f r δ n + saddleJt f r δ n))
        atTop (𝓝 1) := by
    have hadd :
        Tendsto
          (fun n : ℕ =>
            S n * saddleJc f r δ n + S n * saddleJt f r δ n) atTop (𝓝 1) := by
      simpa [S] using Hcentral.add Htail
    refine Tendsto.congr' ?_ hadd
    exact Eventually.of_forall fun n => by
      dsimp [S]
      ring
  exact Tendsto.congr' hratio.symm hsum

/--
Assembly theorem with the exact split discharged from the Cauchy parameterization
and interval additivity.
-/
theorem coeff_isEquivalent_saddle_assembly_of_cauchy
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ} (r B δ : ℕ → ℝ)
    (hp : HasFPowerSeriesAt f p 0)
    (hr : ∀ᶠ n in atTop, 0 < r n)
    (hd : ∀ᶠ n in atTop, DifferentiableOn ℂ f (Metric.closedBall 0 (r n)))
    (hfnz : ∀ᶠ n in atTop, f (r n : ℂ) ≠ 0)
    (hleft : ∀ᶠ n in atTop,
      IntervalIntegrable (saddleG f r n) MeasureTheory.volume (-Real.pi) (-(δ n)))
    (hcenterInt : ∀ᶠ n in atTop,
      IntervalIntegrable (saddleG f r n) MeasureTheory.volume (-(δ n)) (δ n))
    (hright : ∀ᶠ n in atTop,
      IntervalIntegrable (saddleG f r n) MeasureTheory.volume (δ n) Real.pi)
    (Hcentral : Tendsto
      (fun n : ℕ => (Real.sqrt (2 * Real.pi * B n) : ℂ) * saddleJc f r δ n)
      atTop (𝓝 1))
    (Htail : Tendsto
      (fun n : ℕ => (Real.sqrt (2 * Real.pi * B n) : ℂ) * saddleJt f r δ n)
      atTop (𝓝 0))
    (Hnz : ∀ᶠ n in atTop, saddleScale f r B n ≠ 0) :
    (fun n : ℕ => p.coeff n) ~[atTop] (fun n : ℕ => saddleScale f r B n) :=
  coeff_isEquivalent_saddle_assembly r B δ
    (eventually_coeff_eq_saddle_split r δ hp hr hd hfnz hleft hcenterInt hright)
    Hcentral Htail Hnz

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

private lemma Hfun_eq_indicator (f : ℂ → ℂ) (r B δ : ℕ → ℝ) (n : ℕ) :
    Hfun f r B δ n =
      Set.indicator (Set.Icc (-(δ n * Real.sqrt (B n))) (δ n * Real.sqrt (B n)))
        (fun x : ℝ => saddleG f r n (x / Real.sqrt (B n))) := by
  funext x
  simp [Hfun, Set.indicator, abs_le]

private lemma integral_Hfun_eq_interval
    (f : ℂ → ℂ) (r B δ : ℕ → ℝ) (n : ℕ)
    (hL : 0 ≤ δ n * Real.sqrt (B n)) :
    (∫ x : ℝ, Hfun f r B δ n x) =
      ∫ x in -(δ n * Real.sqrt (B n))..(δ n * Real.sqrt (B n)),
        saddleG f r n (x / Real.sqrt (B n)) := by
  let L : ℝ := δ n * Real.sqrt (B n)
  let g : ℝ → ℂ := fun x => saddleG f r n (x / Real.sqrt (B n))
  have hle : -L ≤ L := by linarith [hL]
  calc
    (∫ x : ℝ, Hfun f r B δ n x) =
        ∫ x : ℝ, Set.indicator (Set.Icc (-L) L) g x := by
          simp [Hfun_eq_indicator, L, g]
    _ = ∫ x in Set.Icc (-L) L, g x := by
          rw [MeasureTheory.integral_indicator measurableSet_Icc]
    _ = ∫ x in Set.Ioc (-L) L, g x := by
          rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    _ = ∫ x in (-L)..L, g x := by
          rw [intervalIntegral.integral_of_le hle]

/--
Dominated-convergence central Gaussian core, with the measurability hypothesis
required by Mathlib's DCT stated explicitly.
-/
theorem central_tendsto_one_of_dominated_of_aestronglyMeasurable
    (f : ℂ → ℂ) (r B δ : ℕ → ℝ)
    (hBpos : ∀ᶠ n in atTop, 0 < B n)
    (hL : Tendsto (fun n : ℕ => δ n * Real.sqrt (B n)) atTop atTop)
    (Hmeas :
      ∀ᶠ n in atTop,
        AEStronglyMeasurable (Hfun f r B δ n) MeasureTheory.volume)
    (Hpoint :
      ∀ᵐ x : ℝ,
        Tendsto (fun n : ℕ => Hfun f r B δ n x) atTop
          (𝓝 (Complex.exp (-(x ^ 2) / 2))))
    (D : ℝ → ℝ) (hDint : Integrable D)
    (Hdom :
      ∀ᶠ n in atTop, ∀ᵐ x : ℝ, ‖Hfun f r B δ n x‖ ≤ D x) :
    Tendsto
      (fun n : ℕ => (Real.sqrt (2 * Real.pi * B n) : ℂ) * saddleJc f r δ n)
      atTop (𝓝 1) := by
  have hInt_tendsto :
      Tendsto (fun n : ℕ => ∫ x : ℝ, Hfun f r B δ n x) atTop
        (𝓝 (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2))) := by
    exact MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := MeasureTheory.volume) (bound := D) Hmeas Hdom hDint Hpoint
  have hsqrt2_pos : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hsqrt2_ne : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := by
    exact_mod_cast hsqrt2_pos.ne'
  have hscaled :
      Tendsto
        (fun n : ℕ => (1 / Real.sqrt (2 * Real.pi) : ℂ) *
          ∫ x : ℝ, Hfun f r B δ n x)
        atTop (𝓝 1) := by
    have hmul := hInt_tendsto.const_mul (1 / Real.sqrt (2 * Real.pi) : ℂ)
    have hconst :
        (1 / Real.sqrt (2 * Real.pi) : ℂ) *
          (∫ x : ℝ, Complex.exp (-(x ^ 2) / 2)) = 1 := by
      rw [gaussian_integral_half]
      field_simp [hsqrt2_ne]
    simpa only [hconst] using hmul
  have hLnonneg : ∀ᶠ n in atTop, 0 ≤ δ n * Real.sqrt (B n) :=
    hL.eventually_ge_atTop 0
  have heq :
      (fun n : ℕ => (Real.sqrt (2 * Real.pi * B n) : ℂ) * saddleJc f r δ n)
        =ᶠ[atTop]
      (fun n : ℕ => (1 / Real.sqrt (2 * Real.pi) : ℂ) *
        ∫ x : ℝ, Hfun f r B δ n x) := by
    filter_upwards [hBpos, hLnonneg] with n hBn hLn
    rw [saddleJc_eq_integral_scaled f r δ B n hBn]
    rw [← integral_Hfun_eq_interval f r B δ n hLn]
  exact Tendsto.congr' heq.symm hscaled

end

/-!
# The exponential saddle testbed

This file instantiates the saddle assembly machinery for `f z = exp z`.
The hard local-analysis estimates are isolated as explicitly documented
lemmas: the second-order exponential limit, the central domination estimate,
and the tail estimate.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval

noncomputable section

namespace ExpStirling

lemma expCarrier_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt Complex.exp (PowerSeries.toFMLS expCarrier) (0 : ℂ) := by
  simpa [expSeriesC] using
    (show HasFPowerSeriesAt Complex.exp (PowerSeries.toFMLS expCarrier) (0 : ℂ) by
      simpa [_root_.expCarrier_toFMLS_eq_expSeries] using exp_hasFPowerSeriesAt_zero)

end ExpStirling
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

lemma Hfun_eq_gaussian_mul_saddleLocalRatio
    (f : ℂ → ℂ) (a b : ℝ → ℝ) (R δ : ℕ → ℝ) (n : ℕ) (x : ℝ)
    (hb : 0 < b (R n)) (ha : a (R n) = (n : ℝ))
    (hx : |x| ≤ δ n * Real.sqrt (b (R n))) :
    Hfun f R (fun n => b (R n)) δ n x =
      Complex.exp (-(x ^ 2) / 2) *
        saddleLocalRatio f a b (R n) (x / Real.sqrt (b (R n))) := by
  simpa [Hfun, saddleG, hx] using
    saddleGAt_eq_gaussian_mul_saddleLocalRatio f a b (R n) x n hb ha

lemma theta_mem_local_window_of_scaled_window
    (x δ B : ℝ) (hB : 0 < B)
    (hx : |x| ≤ δ * Real.sqrt B) :
    |x / Real.sqrt B| ≤ δ := by
  have hsqrt : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB
  rw [abs_div, abs_of_pos hsqrt]
  exact (div_le_iff₀ hsqrt).mpr hx

lemma saddleLocalRatio_tendsto_one_of_localUniform
    {F : Filter ℝ} (f : ℂ → ℂ) (a b δr : ℝ → ℝ)
    (R : ℕ → ℝ) (x : ℝ)
    (hR : Tendsto R atTop F)
    (hlocal :
      ∀ ε > 0, ∀ᶠ r in F, ∀ θ : ℝ,
        |θ| ≤ δr r →
          ‖saddleLocalRatio f a b r θ - 1‖ ≤ ε)
    (hBpos : ∀ᶠ n in atTop, 0 < b (R n))
    (hL :
      Tendsto
        (fun n : ℕ => δr (R n) * Real.sqrt (b (R n)))
        atTop atTop) :
    Tendsto
      (fun n : ℕ =>
        saddleLocalRatio f a b (R n) (x / Real.sqrt (b (R n))))
      atTop (𝓝 (1 : ℂ)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  have hlocR :
      ∀ᶠ n in atTop, ∀ θ : ℝ,
        |θ| ≤ δr (R n) →
          ‖saddleLocalRatio f a b (R n) θ - 1‖ ≤ ε / 2 :=
    hR.eventually (hlocal (ε / 2) hε2)
  have hinside :
      ∀ᶠ n in atTop,
        |x| ≤ δr (R n) * Real.sqrt (b (R n)) :=
    hL.eventually_ge_atTop |x|
  filter_upwards [hlocR, hBpos, hinside] with n hloc hBn hxn
  have htheta :
      |x / Real.sqrt (b (R n))| ≤ δr (R n) :=
    theta_mem_local_window_of_scaled_window x (δr (R n)) (b (R n)) hBn hxn
  have hnorm :
      ‖saddleLocalRatio f a b (R n) (x / Real.sqrt (b (R n))) - 1‖ ≤ ε / 2 :=
    hloc _ htheta
  have hdist :
      dist (saddleLocalRatio f a b (R n) (x / Real.sqrt (b (R n)))) 1 ≤ ε / 2 := by
    simpa [dist_eq_norm] using hnorm
  exact lt_of_le_of_lt hdist (half_lt_self hε)

lemma Hfun_pointwise_of_localUniform
    {F : Filter ℝ} (f : ℂ → ℂ) (a b δr : ℝ → ℝ)
    (R : ℕ → ℝ)
    (hR : Tendsto R atTop F)
    (hlocal :
      ∀ ε > 0, ∀ᶠ r in F, ∀ θ : ℝ,
        |θ| ≤ δr r →
          ‖saddleLocalRatio f a b r θ - 1‖ ≤ ε)
    (hBpos : ∀ᶠ n in atTop, 0 < b (R n))
    (hL :
      Tendsto
        (fun n : ℕ => δr (R n) * Real.sqrt (b (R n)))
        atTop atTop)
    (hsaddle : ∀ᶠ n in atTop, a (R n) = (n : ℝ)) :
    ∀ᵐ x : ℝ,
      Tendsto
        (fun n : ℕ =>
          Hfun f R (fun n => b (R n)) (fun n => δr (R n)) n x)
        atTop (𝓝 (Complex.exp (-(x ^ 2) / 2))) := by
  refine ae_of_all _ fun x => ?_
  have hratio :=
    saddleLocalRatio_tendsto_one_of_localUniform
      f a b δr R x hR hlocal hBpos hL
  have hmul :
      Tendsto
        (fun n : ℕ =>
          Complex.exp (-(x ^ 2) / 2) *
            saddleLocalRatio f a b (R n) (x / Real.sqrt (b (R n))))
        atTop (𝓝 (Complex.exp (-(x ^ 2) / 2) * 1)) :=
    tendsto_const_nhds.mul hratio
  have htarget :
      Tendsto
        (fun n : ℕ =>
          Complex.exp (-(x ^ 2) / 2) *
            saddleLocalRatio f a b (R n) (x / Real.sqrt (b (R n))))
        atTop (𝓝 (Complex.exp (-(x ^ 2) / 2))) := by
    simpa using hmul
  have hinside :
      ∀ᶠ n in atTop,
        |x| ≤ δr (R n) * Real.sqrt (b (R n)) :=
    hL.eventually_ge_atTop |x|
  have heq :
      (fun n : ℕ =>
          Hfun f R (fun n => b (R n)) (fun n => δr (R n)) n x) =ᶠ[atTop]
        (fun n : ℕ =>
          Complex.exp (-(x ^ 2) / 2) *
            saddleLocalRatio f a b (R n) (x / Real.sqrt (b (R n)))) := by
    filter_upwards [hBpos, hsaddle, hinside] with n hBn han hxn
    exact Hfun_eq_gaussian_mul_saddleLocalRatio
      f a b R (fun n => δr (R n)) n x hBn han hxn
  exact Tendsto.congr' heq.symm htarget

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

lemma Hfun_aestronglyMeasurable_of_differentiableOn_closedBall
    (f : ℂ → ℂ) (R B δ : ℕ → ℝ) (n : ℕ)
    (hr : 0 ≤ R n)
    (hf : DifferentiableOn ℂ f (Metric.closedBall (0 : ℂ) (R n))) :
    AEStronglyMeasurable (Hfun f R B δ n) volume := by
  classical
  let L : ℝ := δ n * Real.sqrt (B n)
  let g : ℝ → ℂ := fun x => saddleG f R n (x / Real.sqrt (B n))
  have hgcont : Continuous g := by
    have h0 := saddleGAt_continuous_of_differentiableOn_closedBall f (R n) n hr hf
    have hdiv : Continuous fun x : ℝ => x / Real.sqrt (B n) := by
      fun_prop
    simpa [g, saddleG] using h0.comp hdiv
  have hsm : StronglyMeasurable (Set.indicator (Set.Icc (-L) L) g) :=
    hgcont.stronglyMeasurable.indicator measurableSet_Icc
  have heq :
      Hfun f R B δ n =
        Set.indicator (Set.Icc (-L) L) g := by
    funext x
    simp [Hfun, Set.indicator, abs_le, L, g]
  rw [heq]
  exact hsm.aestronglyMeasurable

lemma Hfun_aestronglyMeasurable_eventually_of_sequence
    {F : Filter ℝ} (f : ℂ → ℂ) (R B δ : ℕ → ℝ)
    (hR : Tendsto R atTop F)
    (hrpos : ∀ᶠ r in F, 0 < r)
    (hdiff :
      ∀ᶠ r in F,
        DifferentiableOn ℂ f (Metric.closedBall (0 : ℂ) r)) :
    ∀ᶠ n in atTop,
      AEStronglyMeasurable (Hfun f R B δ n) volume := by
  filter_upwards [hR.eventually hrpos, hR.eventually hdiff] with n hrn hdiffn
  exact Hfun_aestronglyMeasurable_of_differentiableOn_closedBall
    f R B δ n hrn.le hdiffn

lemma centralD_integrable : Integrable centralD := by
  unfold centralD
  have hbase :
      Integrable
        (fun x : ℝ => Real.exp (-(1 / 2 : ℝ) * x ^ 2)) :=
    integrable_exp_neg_mul_sq
      (by norm_num : 0 < (1 / 2 : ℝ))
  have hconst := hbase.const_mul 2
  convert hconst using 1
  funext x
  congr 1
  ring_nf

lemma saddleLocalRatio_norm_le_two_of_norm_sub_one_le_one
    {z : ℂ} (hz : ‖z - 1‖ ≤ (1 : ℝ)) : ‖z‖ ≤ 2 := by
  have hz_eq : z = (z - 1) + 1 := by ring
  calc
    ‖z‖ = ‖(z - 1) + 1‖ := by
      exact congrArg norm hz_eq
    _ ≤ ‖z - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ ≤ 1 + 1 := add_le_add hz (by norm_num)
    _ = 2 := by norm_num

lemma Hfun_dominated_of_localUniform
    {F : Filter ℝ} (f : ℂ → ℂ) (a b δr : ℝ → ℝ)
    (R : ℕ → ℝ)
    (hR : Tendsto R atTop F)
    (hlocal :
      ∀ ε > 0, ∀ᶠ r in F, ∀ θ : ℝ,
        |θ| ≤ δr r →
          ‖saddleLocalRatio f a b r θ - 1‖ ≤ ε)
    (hBpos : ∀ᶠ n in atTop, 0 < b (R n))
    (hsaddle : ∀ᶠ n in atTop, a (R n) = (n : ℝ)) :
    ∀ᶠ n in atTop, ∀ᵐ x : ℝ,
      ‖Hfun f R (fun n => b (R n)) (fun n => δr (R n)) n x‖
        ≤ centralD x := by
  have hlocR :
      ∀ᶠ n in atTop, ∀ θ : ℝ,
        |θ| ≤ δr (R n) →
          ‖saddleLocalRatio f a b (R n) θ - 1‖ ≤ (1 : ℝ) :=
    hR.eventually (hlocal 1 (by norm_num))
  filter_upwards [hlocR, hBpos, hsaddle] with n hloc hBn han
  refine ae_of_all _ fun x => ?_
  by_cases hx : |x| ≤ δr (R n) * Real.sqrt (b (R n))
  · rw [Hfun_eq_gaussian_mul_saddleLocalRatio
      f a b R (fun n => δr (R n)) n x hBn han hx]
    rw [norm_mul]
    have htheta :
        |x / Real.sqrt (b (R n))| ≤ δr (R n) :=
      theta_mem_local_window_of_scaled_window x (δr (R n)) (b (R n)) hBn hx
    have hratio :
        ‖saddleLocalRatio f a b (R n) (x / Real.sqrt (b (R n)))‖ ≤ 2 :=
      saddleLocalRatio_norm_le_two_of_norm_sub_one_le_one (hloc _ htheta)
    have hnormexp :
        ‖Complex.exp (-(x ^ 2) / 2)‖ =
          Real.exp (-(x ^ 2) / 2) := by
      simp [Complex.norm_exp, sq]
    rw [hnormexp]
    calc
      Real.exp (-(x ^ 2) / 2) *
          ‖saddleLocalRatio f a b (R n) (x / Real.sqrt (b (R n)))‖
          ≤ Real.exp (-(x ^ 2) / 2) * 2 :=
            mul_le_mul_of_nonneg_left hratio (Real.exp_pos _).le
      _ = centralD x := by
            simp [centralD, mul_comm]
  · simp [Hfun, hx, centralD]
    positivity

theorem central_tendsto_one_of_hadmissible
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (hr : SaddleSequence hf) :
    Tendsto
      (fun n : ℕ =>
        (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
          saddleJc f hr.r (HAdmissible.Δ hf hr) n)
      atTop (𝓝 1) := by
  have hBpos : ∀ᶠ n in atTop, 0 < HAdmissible.B hf hr n := by
    simpa [HAdmissible.B] using hr.tendsTo.eventually hf.b_pos
  have hL :
      Tendsto
        (fun n : ℕ =>
          HAdmissible.Δ hf hr n * Real.sqrt (HAdmissible.B hf hr n))
        atTop atTop := by
    simpa [HAdmissible.B, HAdmissible.Δ] using
      hf.δ_sqrt_b_tendsto_atTop.comp hr.tendsTo
  have Hmeas :
      ∀ᶠ n in atTop,
        AEStronglyMeasurable
          (Hfun f hr.r (HAdmissible.B hf hr) (HAdmissible.Δ hf hr) n) volume :=
    Hfun_aestronglyMeasurable_eventually_of_sequence
      f hr.r (HAdmissible.B hf hr) (HAdmissible.Δ hf hr)
      hr.tendsTo hf.r_pos hf.differentiableOn
  have Hpoint :
      ∀ᵐ x : ℝ,
        Tendsto
          (fun n : ℕ =>
            Hfun f hr.r (HAdmissible.B hf hr) (HAdmissible.Δ hf hr) n x)
          atTop (𝓝 (Complex.exp (-(x ^ 2) / 2))) := by
    simpa [HAdmissible.B, HAdmissible.Δ] using
      Hfun_pointwise_of_localUniform
        f hf.a hf.b hf.δ hr.r hr.tendsTo hf.local_uniform
        (by simpa [HAdmissible.B] using hBpos)
        (by simpa [HAdmissible.B, HAdmissible.Δ] using hL)
        hr.saddle_eq
  have Hdom :
      ∀ᶠ n in atTop, ∀ᵐ x : ℝ,
        ‖Hfun f hr.r (HAdmissible.B hf hr) (HAdmissible.Δ hf hr) n x‖
          ≤ centralD x := by
    simpa [HAdmissible.B, HAdmissible.Δ] using
      Hfun_dominated_of_localUniform
        f hf.a hf.b hf.δ hr.r hr.tendsTo hf.local_uniform
        (by simpa [HAdmissible.B] using hBpos)
        hr.saddle_eq
  exact central_tendsto_one_of_dominated_of_aestronglyMeasurable
    f hr.r (HAdmissible.B hf hr) (HAdmissible.Δ hf hr)
    hBpos hL Hmeas Hpoint centralD centralD_integrable Hdom

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

lemma tail_tendsto_zero_of_tailUniform
    (f : ℂ → ℂ) (R B Δ E : ℕ → ℝ)
    (hBpos : ∀ᶠ n in atTop, 0 < B n)
    (hδ_nonneg : ∀ᶠ n in atTop, 0 ≤ Δ n)
    (hδπ : ∀ᶠ n in atTop, Δ n ≤ Real.pi)
    (hE_nonneg : ∀ᶠ n in atTop, 0 ≤ E n)
    (htail : ∀ᶠ n in atTop, ∀ θ : ℝ,
      Δ n ≤ |θ| → |θ| ≤ Real.pi → ‖saddleG f R n θ‖ ≤ E n)
    (hdecay : Tendsto
      (fun n : ℕ => Real.sqrt (2 * Real.pi * B n) * E n) atTop (𝓝 0)) :
    Tendsto
      (fun n : ℕ => (Real.sqrt (2 * Real.pi * B n) : ℂ) * saddleJt f R Δ n)
      atTop (𝓝 0) := by
  let K : ℝ := ‖((2 * Real.pi : ℂ)⁻¹)‖ * (2 * Real.pi)
  have hdecayK :
      Tendsto (fun n : ℕ => K * (Real.sqrt (2 * Real.pi * B n) * E n))
        atTop (𝓝 0) := by
    simpa using hdecay.const_mul K
  have hbound :
      ∀ᶠ n in atTop,
        ‖(Real.sqrt (2 * Real.pi * B n) : ℂ) * saddleJt f R Δ n‖ ≤
          K * (Real.sqrt (2 * Real.pi * B n) * E n) := by
    filter_upwards [hBpos, hδ_nonneg, hδπ, hE_nonneg, htail] with
      n hBn hδn hδπn hEn htailn
    have hJ : ‖saddleJt f R Δ n‖ ≤ K * E n := by
      simpa [saddleJt, saddleG, K] using
        saddleJtAt_norm_le_of_tail_bound f (R n) (Δ n) (E n) n
          hδn hδπn hEn (fun θ hδθ hθπ => htailn θ hδθ hθπ)
    calc
      ‖(Real.sqrt (2 * Real.pi * B n) : ℂ) * saddleJt f R Δ n‖
          = Real.sqrt (2 * Real.pi * B n) * ‖saddleJt f R Δ n‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ Real.sqrt (2 * Real.pi * B n) * (K * E n) :=
            mul_le_mul_of_nonneg_left hJ (Real.sqrt_nonneg _)
      _ = K * (Real.sqrt (2 * Real.pi * B n) * E n) := by
            ring
  have hnorm :
      Tendsto
        (fun n : ℕ =>
          ‖(Real.sqrt (2 * Real.pi * B n) : ℂ) * saddleJt f R Δ n‖)
        atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound hdecayK
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact hnorm

theorem tail_tendsto_zero_of_hadmissible
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (hr : SaddleSequence hf) :
    Tendsto
      (fun n : ℕ =>
        (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
          saddleJt f hr.r (HAdmissible.Δ hf hr) n)
      atTop (𝓝 0) := by
  rcases hf.tail_uniform with ⟨E, hE_nonneg, hdecay, htail⟩
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
  have hdecaySeq :
      Tendsto
        (fun n : ℕ =>
          Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) * E (hr.r n))
        atTop (𝓝 0) := by
    simpa [HAdmissible.B] using hdecay.comp hr.tendsTo
  exact tail_tendsto_zero_of_tailUniform
    f hr.r (HAdmissible.B hf hr) (HAdmissible.Δ hf hr) (fun n => E (hr.r n))
    hBpos hδ_nonneg hδπ hE_nonneg_seq htailSeq hdecaySeq

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

theorem coeff_isEquivalent_saddle_of_hadmissible_limits
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (hr : SaddleSequence hf)
    (Hcentral : Tendsto
      (fun n : ℕ => (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
        saddleJc f hr.r (HAdmissible.Δ hf hr) n) atTop (𝓝 1))
    (Htail : Tendsto
      (fun n : ℕ => (Real.sqrt (2 * Real.pi * HAdmissible.B hf hr n) : ℂ) *
        saddleJt f hr.r (HAdmissible.Δ hf hr) n) atTop (𝓝 0)) :
    (fun n : ℕ => p.coeff n) ~[atTop]
      (fun n : ℕ => saddleScale f hr.r (HAdmissible.B hf hr) n) := by
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
  have hBpos : ∀ᶠ n in atTop, 0 < HAdmissible.B hf hr n := by
    simpa [HAdmissible.B] using hr.tendsTo.eventually hf.b_pos
  have Hnz : ∀ᶠ n in atTop, saddleScale f hr.r (HAdmissible.B hf hr) n ≠ 0 := by
    filter_upwards [hrpos, hr.tendsTo.eventually hf.f_pos, hBpos] with n hrn hfn hBn
    exact saddleScale_nonzero_of_pos f hr.r (HAdmissible.B hf hr) n hrn hfn hBn
  exact coeff_isEquivalent_saddle_assembly_of_cauchy
    hr.r (HAdmissible.B hf hr) (HAdmissible.Δ hf hr)
    hf.hp hrpos hdiff hfnz hleft hcenter hright Hcentral Htail Hnz

theorem coeff_isEquivalent_saddle
    {f : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hf : HAdmissible f p) (hr : SaddleSequence hf) :
    (fun n : ℕ => p.coeff n) ~[atTop]
      (fun n : ℕ => saddleScale f hr.r (HAdmissible.B hf hr) n) :=
  coeff_isEquivalent_saddle_of_hadmissible_limits hf hr
    (central_tendsto_one_of_hadmissible hf hr)
    (tail_tendsto_zero_of_hadmissible hf hr)

end

/-!
# Involution H-admissible saddle data

This file records the Hayman data for the involution EGF
`exp (z + z^2 / 2)`.  The saddle data are
`a(r)=r+r^2`, `b(r)=r+2r^2`, and `δ(r)=r^(-3/4)`.
-/

open Complex Filter Asymptotics MeasureTheory
open scoped Topology Real NNReal ENNReal Interval PowerSeries

noncomputable section

namespace InvolutionHAdmissible

/-- The genuine complex EGF carrier coming from the Ch2 involution class. -/
def involCarrier : PowerSeries ℂ :=
  PowerSeries.mapℂ AnalyticCombinatorics.Ch1.CombClass.parts12.set.egf

@[simp] theorem involCarrier_coeff (n : ℕ) :
    PowerSeries.coeff (R := ℂ) n involCarrier = (involCoeffR n : ℂ) := by
  simp [involCarrier, involCoeffR, AnalyticCombinatorics.Ch1.CombClass.coeff_egf]

/-- The formal series used by the H-admissible interface. -/
noncomputable abbrev involSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  PowerSeries.toFMLS involCarrier

/-- The quadratic inner PowerSeries `z + z^2/2`. -/
def involInnerPS : PowerSeries ℂ :=
  (PowerSeries.X : PowerSeries ℂ) + (2⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 2

lemma involInnerPS_constantCoeff : PowerSeries.constantCoeff involInnerPS = 0 := by
  unfold involInnerPS
  have hX : PowerSeries.constantCoeff (R := ℂ) (PowerSeries.X : PowerSeries ℂ) = 0 :=
    _root_.PowerSeries.constantCoeff_X
  have hpow : PowerSeries.constantCoeff (R := ℂ) ((PowerSeries.X : PowerSeries ℂ) ^ 2) =
      (PowerSeries.constantCoeff (R := ℂ) (PowerSeries.X : PowerSeries ℂ)) ^ 2 :=
    _root_.map_pow (PowerSeries.constantCoeff (R := ℂ)) (PowerSeries.X : PowerSeries ℂ) 2
  have hpow0 : PowerSeries.constantCoeff (R := ℂ) ((PowerSeries.X : PowerSeries ℂ) ^ 2) = 0 :=
    hpow.trans ((congrArg (fun z : ℂ => z ^ 2) hX).trans (by norm_num))
  have hsmul : PowerSeries.constantCoeff (R := ℂ)
      ((2⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 2) =
        (2⁻¹ : ℂ) • PowerSeries.constantCoeff (R := ℂ) ((PowerSeries.X : PowerSeries ℂ) ^ 2) :=
    _root_.PowerSeries.constantCoeff_smul ((PowerSeries.X : PowerSeries ℂ) ^ 2) (2⁻¹ : ℂ)
  have hsmul0 : PowerSeries.constantCoeff (R := ℂ)
      ((2⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 2) = 0 :=
    hsmul.trans ((congrArg (fun z : ℂ => (2⁻¹ : ℂ) • z) hpow0).trans (smul_zero _))
  have hadd : PowerSeries.constantCoeff (R := ℂ)
      ((PowerSeries.X : PowerSeries ℂ) + (2⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 2) =
        PowerSeries.constantCoeff (R := ℂ) (PowerSeries.X : PowerSeries ℂ) +
          PowerSeries.constantCoeff (R := ℂ) ((2⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 2) :=
    _root_.map_add (PowerSeries.constantCoeff (R := ℂ))
      (PowerSeries.X : PowerSeries ℂ) ((2⁻¹ : ℂ) • (PowerSeries.X : PowerSeries ℂ) ^ 2)
  exact hadd.trans
    ((congrArg₂ (fun x y : ℂ => x + y) hX hsmul0).trans (add_zero (0 : ℂ)))

theorem involCarrier_eq_complex_subst :
    involCarrier = (PowerSeries.exp ℂ).subst involInnerPS := by
  rw [involCarrier, AnalyticCombinatorics.Ch1.CombClass.egf_involutions]
  have hsubst : PowerSeries.HasSubst
      ((PowerSeries.X : PowerSeries ℚ) + (2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2) := by
    apply PowerSeries.HasSubst.of_constantCoeff_zero'
    have hX : PowerSeries.constantCoeff (R := ℚ) (PowerSeries.X : PowerSeries ℚ) = 0 :=
      _root_.PowerSeries.constantCoeff_X
    have hpow : PowerSeries.constantCoeff (R := ℚ) ((PowerSeries.X : PowerSeries ℚ) ^ 2) =
        (PowerSeries.constantCoeff (R := ℚ) (PowerSeries.X : PowerSeries ℚ)) ^ 2 :=
      _root_.map_pow (PowerSeries.constantCoeff (R := ℚ)) (PowerSeries.X : PowerSeries ℚ) 2
    have hpow0 : PowerSeries.constantCoeff (R := ℚ) ((PowerSeries.X : PowerSeries ℚ) ^ 2) = 0 :=
      hpow.trans ((congrArg (fun z : ℚ => z ^ 2) hX).trans (by norm_num))
    have hsmul : PowerSeries.constantCoeff (R := ℚ)
        ((2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2) =
          (2⁻¹ : ℚ) • PowerSeries.constantCoeff (R := ℚ) ((PowerSeries.X : PowerSeries ℚ) ^ 2) :=
      _root_.PowerSeries.constantCoeff_smul ((PowerSeries.X : PowerSeries ℚ) ^ 2) (2⁻¹ : ℚ)
    have hsmul0 : PowerSeries.constantCoeff (R := ℚ)
        ((2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2) = 0 :=
      hsmul.trans ((congrArg (fun z : ℚ => (2⁻¹ : ℚ) • z) hpow0).trans (smul_zero _))
    have hadd : PowerSeries.constantCoeff (R := ℚ)
        ((PowerSeries.X : PowerSeries ℚ) + (2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2) =
          PowerSeries.constantCoeff (R := ℚ) (PowerSeries.X : PowerSeries ℚ) +
            PowerSeries.constantCoeff (R := ℚ) ((2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2) :=
      _root_.map_add (PowerSeries.constantCoeff (R := ℚ))
        (PowerSeries.X : PowerSeries ℚ) ((2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2)
    exact hadd.trans
      ((congrArg₂ (fun x y : ℚ => x + y) hX hsmul0).trans (add_zero (0 : ℚ)))
  have hmap_inner :
      (((PowerSeries.X : PowerSeries ℚ) +
          (2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2).map (algebraMap ℚ ℂ)) =
        involInnerPS := by
    ext n
    by_cases hn : n = 2
    · subst n
      norm_num [involInnerPS, PowerSeries.coeff_map, PowerSeries.coeff_X_pow]
    · simp [involInnerPS, PowerSeries.coeff_map, PowerSeries.coeff_X_pow, hn]
  have hmap_exp :
      (PowerSeries.exp ℚ).map (algebraMap ℚ ℂ) = PowerSeries.exp ℂ := by
    ext n
    simp
  change (((PowerSeries.exp ℚ).subst
        ((PowerSeries.X : PowerSeries ℚ) + (2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2)).map
      (algebraMap ℚ ℂ)) = _
  rw [PowerSeries.map_subst
    (a := ((PowerSeries.X : PowerSeries ℚ) +
      (2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2))
    (h := algebraMap ℚ ℂ) hsubst (PowerSeries.exp ℚ)]
  rw [hmap_exp]
  change (PowerSeries.exp ℂ).subst
      ((((PowerSeries.X : PowerSeries ℚ) +
        (2⁻¹ : ℚ) • (PowerSeries.X : PowerSeries ℚ) ^ 2).map (algebraMap ℚ ℂ))) =
    (PowerSeries.exp ℂ).subst involInnerPS
  rw [hmap_inner]

lemma hasFPowerSeriesAt_id_toFMLS_X :
    HasFPowerSeriesAt (fun z : ℂ => z)
      (PowerSeries.toFMLS (PowerSeries.X : PowerSeries ℂ)) (0 : ℂ) := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards with z
  let term : ℕ → ℂ :=
    fun n => z ^ n • (PowerSeries.toFMLS (PowerSeries.X : PowerSeries ℂ)).coeff n
  have hsingle : HasSum term (term 1) := by
    apply hasSum_single
    intro n hn
    simp [term, PowerSeries.coeff_X, hn]
  convert hsingle using 1
  simp [term, PowerSeries.toFMLS]

lemma hasFPowerSeriesAt_mul_toFMLS {f g : ℂ → ℂ} {F G : PowerSeries ℂ}
    (hf : HasFPowerSeriesAt f (PowerSeries.toFMLS F) (0 : ℂ))
    (hg : HasFPowerSeriesAt g (PowerSeries.toFMLS G) (0 : ℂ)) :
    HasFPowerSeriesAt (fun z : ℂ => f z * g z)
      (PowerSeries.toFMLS (F * G)) (0 : ℂ) := by
  rcases hf with ⟨rf, hrf⟩
  rcases hg with ⟨rg, hrg⟩
  rw [hasFPowerSeriesAt_iff]
  refine eventually_of_mem
    (Metric.eball_mem_nhds (0 : ℂ) (lt_min hrf.r_pos hrg.r_pos)) ?_
  intro z hz
  have hzf : z ∈ Metric.eball (0 : ℂ) rf := by
    exact Metric.mem_eball.mpr
      (lt_of_lt_of_le (Metric.mem_eball.mp hz) (min_le_left _ _))
  have hzg : z ∈ Metric.eball (0 : ℂ) rg := by
    exact Metric.mem_eball.mpr
      (lt_of_lt_of_le (Metric.mem_eball.mp hz) (min_le_right _ _))
  let a : ℕ → ℂ := fun n => z ^ n * PowerSeries.coeff (R := ℂ) n F
  let b : ℕ → ℂ := fun n => z ^ n * PowerSeries.coeff (R := ℂ) n G
  have hsumf : HasSum a (f z) := by
    have h := hrf.hasSum hzf
    simpa [a, PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using h
  have hsumg : HasSum b (g z) := by
    have h := hrg.hasSum hzg
    simpa [b, PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using h
  have hzfrad : z ∈ Metric.eball (0 : ℂ) (PowerSeries.toFMLS F).radius :=
    Metric.eball_subset_eball hrf.r_le hzf
  have hzgrad : z ∈ Metric.eball (0 : ℂ) (PowerSeries.toFMLS G).radius :=
    Metric.eball_subset_eball hrg.r_le hzg
  have hnormf : Summable fun n : ℕ => ‖a n‖ := by
    simpa [a, PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using
      (PowerSeries.toFMLS F).summable_norm_apply hzfrad
  have hnormg : Summable fun n : ℕ => ‖b n‖ := by
    simpa [b, PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using
      (PowerSeries.toFMLS G).summable_norm_apply hzgrad
  let cseq : ℕ → ℂ := fun n => z ^ n * PowerSeries.coeff (R := ℂ) n (F * G)
  let d : ℕ → ℂ := fun n => ∑ kl ∈ Finset.antidiagonal n, a kl.1 * b kl.2
  have hcd : ∀ n, cseq n = d n := by
    intro n
    change z ^ n * PowerSeries.coeff (R := ℂ) n (F * G) =
      ∑ kl ∈ Finset.antidiagonal n, a kl.1 * b kl.2
    rw [PowerSeries.coeff_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro kl hkl
    have hsum : kl.1 + kl.2 = n := Finset.mem_antidiagonal.mp hkl
    simp [a, b]
    rw [← hsum, pow_add]
    ring
  have hnormd : Summable fun n : ℕ => ‖d n‖ := by
    simpa [d] using summable_norm_sum_mul_antidiagonal_of_summable_norm hnormf hnormg
  have hnormc : Summable fun n : ℕ => ‖cseq n‖ := by
    exact hnormd.congr (fun n => by rw [hcd n])
  have hsumc : Summable cseq := hnormc.of_norm
  have htsum : (∑' n : ℕ, cseq n) = f z * g z := by
    have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hnormf hnormg
    rw [hsumf.tsum_eq, hsumg.tsum_eq] at hprod
    rw [tsum_congr hcd, ← hprod]
  have hmain : HasSum cseq (f z * g z) := hsumc.hasSum_iff.mpr htsum
  simpa [cseq, PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars, smul_eq_mul,
    mul_comm, mul_left_comm, mul_assoc] using hmain

lemma involInner_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt (fun z : ℂ => z + z ^ 2 / 2)
      (PowerSeries.toFMLS involInnerPS) (0 : ℂ) := by
  have hX : HasFPowerSeriesAt (fun z : ℂ => z)
      (PowerSeries.toFMLS (PowerSeries.X : PowerSeries ℂ)) (0 : ℂ) :=
    hasFPowerSeriesAt_id_toFMLS_X
  have hX2 : HasFPowerSeriesAt (fun z : ℂ => z * z)
      (PowerSeries.toFMLS ((PowerSeries.X : PowerSeries ℂ) ^ 2)) (0 : ℂ) := by
    simpa [pow_two] using hasFPowerSeriesAt_mul_toFMLS hX hX
  have hhalf : HasFPowerSeriesAt (fun z : ℂ => (2⁻¹ : ℂ) • (z * z))
      ((2⁻¹ : ℂ) • PowerSeries.toFMLS ((PowerSeries.X : PowerSeries ℂ) ^ 2)) (0 : ℂ) := by
    simpa using (HasFPowerSeriesAt.const_smul (c := (2⁻¹ : ℂ)) hX2)
  have hsum := hX.add hhalf
  have hseries :
      PowerSeries.toFMLS involInnerPS =
        PowerSeries.toFMLS (PowerSeries.X : PowerSeries ℂ) +
          (2⁻¹ : ℂ) • PowerSeries.toFMLS ((PowerSeries.X : PowerSeries ℂ) ^ 2) := by
    ext n
    simp [involInnerPS, PowerSeries.toFMLS, FormalMultilinearSeries.ofScalars]
  rw [hseries]
  convert hsum using 1
  funext z
  simp [smul_eq_mul]
  ring_nf

lemma involFun_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt involFun involSeries (0 : ℂ) := by
  have houter : HasFPowerSeriesAt Complex.exp (PowerSeries.toFMLS (PowerSeries.exp ℂ))
      ((fun z : ℂ => z + z ^ 2 / 2) 0) := by
    simpa using ExpStirling.expCarrier_hasFPowerSeriesAt_zero
  have hcomp := HasFPowerSeriesAt.comp (g := Complex.exp)
    (f := fun z : ℂ => z + z ^ 2 / 2) houter involInner_hasFPowerSeriesAt_zero
  change HasFPowerSeriesAt involFun (PowerSeries.toFMLS involCarrier) (0 : ℂ)
  rw [involCarrier_eq_complex_subst]
  rw [PowerSeries.toFMLS_subst_eq_comp involInnerPS_constantCoeff]
  simpa [Function.comp_def, involFun, involSeries] using hcomp

/-- Continuous involution saddle mean, `a(r)=r+r^2`. -/
def involSaddleAReal (r : ℝ) : ℝ :=
  r + r ^ 2

/-- Hayman window for the involution saddle. -/
def involSaddleDeltaReal (r : ℝ) : ℝ :=
  r ^ (-(3 / 4 : ℝ))

@[simp] lemma involSaddleAReal_apply (r : ℝ) :
    involSaddleAReal r = r + r ^ 2 := rfl

@[simp] lemma involSaddleBReal_apply (r : ℝ) :
    involSaddleBReal r = r + 2 * r ^ 2 := rfl

@[simp] lemma involSaddleDeltaReal_apply (r : ℝ) :
    involSaddleDeltaReal r = r ^ (-(3 / 4 : ℝ)) := rfl

/-- The exact exponent left after removing the linear and quadratic saddle terms. -/
def involLocalExponent (r θ : ℝ) : ℂ :=
  (r : ℂ) * ExpStirling.expLocalRemainder θ +
    (((r ^ 2 / 2 : ℝ) : ℂ) * ExpStirling.expLocalRemainder (2 * θ))

lemma complex_two_mul_theta_I (θ : ℝ) :
    (((2 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I)) =
      ((2 * θ : ℝ) : ℂ) * Complex.I := by
  simp [Complex.ofReal_mul, mul_assoc, mul_comm]

lemma invol_saddleLocalRatio_eq (r θ : ℝ) :
    saddleLocalRatio involFun involSaddleAReal involSaddleBReal r θ =
      Complex.exp (involLocalExponent r θ) := by
  unfold saddleLocalRatio involFun involLocalExponent involSaddleAReal involSaddleBReal
  have hsq_full :
      ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ 2 =
        ((r ^ 2 : ℝ) : ℂ) * Complex.exp ((2 * θ : ℝ) * Complex.I) := by
    rw [mul_pow, ← Complex.exp_nat_mul]
    rw [show (r : ℂ) ^ 2 = ((r ^ 2 : ℝ) : ℂ) by norm_num]
    rw [show (((2 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I)) =
        ((2 * θ : ℝ) : ℂ) * Complex.I by
      simpa using complex_two_mul_theta_I θ]
  rw [← Complex.exp_sub]
  rw [← Complex.exp_add]
  rw [← Complex.exp_sub]
  congr 1
  rw [ExpStirling.expLocalRemainder_eq θ]
  rw [ExpStirling.expLocalRemainder_eq (2 * θ)]
  rw [hsq_full]
  norm_num [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_pow]
  ring_nf

lemma invol_f_pos_eventually :
    ∀ᶠ r : ℝ in atTop, 0 < (involFun (r : ℂ)).re := by
  refine Eventually.of_forall fun r => ?_
  unfold involFun
  have harg : (r : ℂ) + (r : ℂ) ^ 2 / 2 = ((r + r ^ 2 / 2 : ℝ) : ℂ) := by
    norm_num
  have hval :
      Complex.exp (((r + r ^ 2 / 2 : ℝ) : ℂ)) =
        ((Real.exp (r + r ^ 2 / 2) : ℝ) : ℂ) := by
    simp
  rw [harg, hval]
  exact Real.exp_pos (r + r ^ 2 / 2)

lemma invol_b_pos_eventually :
    ∀ᶠ r : ℝ in atTop, 0 < involSaddleBReal r := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  unfold involSaddleBReal
  positivity

lemma invol_delta_pos_eventually :
    ∀ᶠ r : ℝ in atTop, 0 < involSaddleDeltaReal r := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  unfold involSaddleDeltaReal
  exact Real.rpow_pos_of_pos hr _

lemma invol_delta_tendsto_zero :
    Tendsto involSaddleDeltaReal atTop (𝓝 0) := by
  simpa [involSaddleDeltaReal] using
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 4))

lemma invol_delta_le_pi_eventually :
    ∀ᶠ r : ℝ in atTop, involSaddleDeltaReal r ≤ Real.pi :=
  invol_delta_tendsto_zero.eventually_le_const Real.pi_pos

lemma invol_delta_le_one_eventually :
    ∀ᶠ r : ℝ in atTop, involSaddleDeltaReal r ≤ 1 :=
  invol_delta_tendsto_zero.eventually_le_const zero_lt_one

lemma invol_delta_mul_r_eq_rpow_eventually :
    (fun r : ℝ => involSaddleDeltaReal r * r) =ᶠ[atTop]
      fun r : ℝ => r ^ (1 / 4 : ℝ) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  calc
    involSaddleDeltaReal r * r
        = r ^ (-(3 / 4 : ℝ)) * r ^ (1 : ℝ) := by
          simp [involSaddleDeltaReal, Real.rpow_one]
    _ = r ^ (-(3 / 4 : ℝ) + (1 : ℝ)) := by
          rw [Real.rpow_add hr]
    _ = r ^ (1 / 4 : ℝ) := by norm_num

lemma invol_delta_sqrt_b_tendsto_atTop :
    Tendsto (fun r : ℝ => involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r))
      atTop atTop := by
  have hpow : Tendsto (fun r : ℝ => r ^ (1 / 4 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)
  refine tendsto_atTop_mono' atTop ?_ hpow
  filter_upwards [eventually_ge_atTop (1 : ℝ), invol_delta_mul_r_eq_rpow_eventually] with
    r hr heq
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hb_ge : r ^ 2 ≤ involSaddleBReal r := by
    unfold involSaddleBReal
    nlinarith [sq_nonneg r]
  have hsqrt_ge : r ≤ Real.sqrt (involSaddleBReal r) := by
    exact Real.le_sqrt_of_sq_le hb_ge
  have hδ_nonneg : 0 ≤ involSaddleDeltaReal r := by
    unfold involSaddleDeltaReal
    positivity
  calc
    r ^ (1 / 4 : ℝ) = involSaddleDeltaReal r * r := heq.symm
    _ ≤ involSaddleDeltaReal r * Real.sqrt (involSaddleBReal r) :=
      mul_le_mul_of_nonneg_left hsqrt_ge hδ_nonneg

lemma invol_differentiableOn_eventually :
    ∀ᶠ r : ℝ in atTop,
      DifferentiableOn ℂ involFun (Metric.closedBall (0 : ℂ) r) := by
  refine Eventually.of_forall fun r => ?_
  unfold involFun
  fun_prop

def involLocalControl (r : ℝ) : ℝ :=
  r ^ 2 * (involSaddleDeltaReal r) ^ 3

lemma involLocalControl_eq_rpow_eventually :
    involLocalControl =ᶠ[atTop] fun r : ℝ => r ^ (-(1 / 4 : ℝ)) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have hr0 : 0 ≤ r := hr.le
  have hr2_rpow : r ^ 2 = r ^ (2 : ℝ) := by
    exact (Real.rpow_natCast r 2).symm
  have hdelta_pow :
      (r ^ (-(3 / 4 : ℝ))) ^ 3 = r ^ (-(3 / 4 : ℝ) * (3 : ℝ)) :=
    (Real.rpow_mul_natCast hr0 (-(3 / 4 : ℝ)) 3).symm
  unfold involLocalControl involSaddleDeltaReal
  calc
    r ^ 2 * (r ^ (-(3 / 4 : ℝ))) ^ 3
        = r ^ (2 : ℝ) * r ^ (-(3 / 4 : ℝ) * (3 : ℝ)) := by
          rw [hr2_rpow, hdelta_pow]
    _ = r ^ ((2 : ℝ) + (-(3 / 4 : ℝ) * (3 : ℝ))) := by
          rw [Real.rpow_add hr]
    _ = r ^ (-(1 / 4 : ℝ)) := by norm_num

lemma involLocalControl_tendsto_zero :
    Tendsto involLocalControl atTop (𝓝 0) := by
  have hpow : Tendsto (fun r : ℝ => r ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)
  exact Tendsto.congr' involLocalControl_eq_rpow_eventually.symm hpow

def involLocalConstant : ℝ :=
  40 * Real.exp 2

lemma involLocalBound_tendsto_zero :
    Tendsto (fun r : ℝ => involLocalConstant * involLocalControl r) atTop (𝓝 0) := by
  simpa using involLocalControl_tendsto_zero.const_mul involLocalConstant

lemma expLocalRemainder_norm_le_exp_two {θ : ℝ} (hθ : |θ| ≤ 2) :
    ‖ExpStirling.expLocalRemainder θ‖ ≤ Real.exp 2 * |θ| ^ 3 := by
  calc
    ‖ExpStirling.expLocalRemainder θ‖ ≤ |θ| ^ 3 * Real.exp |θ| :=
      ExpStirling.expLocalRemainder_norm_le θ
    _ ≤ |θ| ^ 3 * Real.exp 2 := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hθ)
        (pow_nonneg (abs_nonneg θ) 3)
    _ = Real.exp 2 * |θ| ^ 3 := by ring

lemma invol_local_exponent_norm_le_eventually :
    ∀ᶠ r : ℝ in atTop, ∀ θ : ℝ, |θ| ≤ involSaddleDeltaReal r →
      ‖involLocalExponent r θ‖ ≤ involLocalConstant * involLocalControl r := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), invol_delta_le_one_eventually] with
    r hr hδ_le_one θ hθδ
  let δ : ℝ := involSaddleDeltaReal r
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hδ0 : 0 ≤ δ := by
    dsimp [δ, involSaddleDeltaReal]
    positivity
  have hθ_one : |θ| ≤ 1 := hθδ.trans hδ_le_one
  have hθ_two : |θ| ≤ 2 := hθ_one.trans (by norm_num)
  have h2θ_two : |2 * θ| ≤ 2 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hθ_one]
  have hθ3δ3 : |θ| ^ 3 ≤ δ ^ 3 :=
    pow_le_pow_left₀ (abs_nonneg θ) hθδ 3
  have h2θ3 : |2 * θ| ^ 3 ≤ 8 * δ ^ 3 := by
    calc
      |2 * θ| ^ 3 = 8 * |θ| ^ 3 := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        ring_nf
      _ ≤ 8 * δ ^ 3 := mul_le_mul_of_nonneg_left hθ3δ3 (by norm_num)
  have hrem1 := expLocalRemainder_norm_le_exp_two hθ_two
  have hrem2 := expLocalRemainder_norm_le_exp_two h2θ_two
  have hterm1 :
      ‖(r : ℂ) * ExpStirling.expLocalRemainder θ‖ ≤
        Real.exp 2 * (r * δ ^ 3) := by
    calc
      ‖(r : ℂ) * ExpStirling.expLocalRemainder θ‖
          = r * ‖ExpStirling.expLocalRemainder θ‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
      _ ≤ r * (Real.exp 2 * |θ| ^ 3) :=
        mul_le_mul_of_nonneg_left hrem1 hr0
      _ ≤ r * (Real.exp 2 * δ ^ 3) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hθ3δ3 (Real.exp_pos 2).le) hr0
      _ = Real.exp 2 * (r * δ ^ 3) := by ring_nf
  have hterm2 :
      ‖(((r ^ 2 / 2 : ℝ) : ℂ) * ExpStirling.expLocalRemainder (2 * θ))‖ ≤
        4 * Real.exp 2 * (r ^ 2 * δ ^ 3) := by
    have hcoef0 : 0 ≤ r ^ 2 / 2 := by positivity
    calc
      ‖(((r ^ 2 / 2 : ℝ) : ℂ) * ExpStirling.expLocalRemainder (2 * θ))‖
          = (r ^ 2 / 2) * ‖ExpStirling.expLocalRemainder (2 * θ)‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcoef0]
      _ ≤ (r ^ 2 / 2) * (Real.exp 2 * |2 * θ| ^ 3) :=
        mul_le_mul_of_nonneg_left hrem2 hcoef0
      _ ≤ (r ^ 2 / 2) * (Real.exp 2 * (8 * δ ^ 3)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h2θ3 (Real.exp_pos 2).le) hcoef0
      _ = 4 * Real.exp 2 * (r ^ 2 * δ ^ 3) := by ring
  have hterm1' :
      Real.exp 2 * (r * δ ^ 3) ≤ Real.exp 2 * (r ^ 2 * δ ^ 3) := by
    have hr_le_r2 : r ≤ r ^ 2 := by nlinarith [hr]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hr_le_r2 (pow_nonneg hδ0 3)) (Real.exp_pos 2).le
  calc
    ‖involLocalExponent r θ‖
        ≤ ‖(r : ℂ) * ExpStirling.expLocalRemainder θ‖ +
          ‖(((r ^ 2 / 2 : ℝ) : ℂ) * ExpStirling.expLocalRemainder (2 * θ))‖ :=
        norm_add_le _ _
    _ ≤ Real.exp 2 * (r * δ ^ 3) + 4 * Real.exp 2 * (r ^ 2 * δ ^ 3) :=
        add_le_add hterm1 hterm2
    _ ≤ Real.exp 2 * (r ^ 2 * δ ^ 3) + 4 * Real.exp 2 * (r ^ 2 * δ ^ 3) :=
        add_le_add hterm1' (le_refl _)
    _ = 5 * Real.exp 2 * (r ^ 2 * δ ^ 3) := by ring_nf
    _ ≤ involLocalConstant * involLocalControl r := by
      unfold involLocalConstant involLocalControl
      dsimp [δ]
      have hnonneg : 0 ≤ r ^ 2 * (r ^ (-(3 / 4 : ℝ))) ^ 3 := by
        positivity
      nlinarith [Real.exp_pos 2, hnonneg]

lemma invol_local_uniform :
    ∀ ε > 0, ∀ᶠ (r : ℝ) in atTop, ∀ θ : ℝ,
      |θ| ≤ involSaddleDeltaReal r →
        ‖saddleLocalRatio involFun involSaddleAReal involSaddleBReal r θ - 1‖ ≤ ε := by
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have hsmall :
      ∀ᶠ r : ℝ in atTop, involLocalConstant * involLocalControl r ≤ ε / 2 :=
    involLocalBound_tendsto_zero.eventually_le_const hhalf
  have hone :
      ∀ᶠ r : ℝ in atTop, involLocalConstant * involLocalControl r ≤ 1 :=
    involLocalBound_tendsto_zero.eventually_le_const zero_lt_one
  filter_upwards [invol_local_exponent_norm_le_eventually, hsmall, hone] with
    r hloc hsmallr honer θ hθ
  rw [invol_saddleLocalRatio_eq]
  have hz : ‖involLocalExponent r θ‖ ≤ involLocalConstant * involLocalControl r :=
    hloc θ hθ
  have hz_one : ‖involLocalExponent r θ‖ ≤ 1 := hz.trans honer
  calc
    ‖Complex.exp (involLocalExponent r θ) - 1‖
        ≤ 2 * ‖involLocalExponent r θ‖ :=
          Complex.norm_exp_sub_one_le hz_one
    _ ≤ 2 * (involLocalConstant * involLocalControl r) :=
          mul_le_mul_of_nonneg_left hz (by norm_num)
    _ ≤ ε := by linarith

lemma invol_saddleGAt_norm (r : ℝ) (n : ℕ) (θ : ℝ) :
    ‖saddleGAt involFun r n θ‖ =
      Real.exp (r * (Real.cos θ - 1) + (r ^ 2 / 2) * (Real.cos (2 * θ) - 1)) := by
  unfold saddleGAt involFun
  have hphase : ‖Complex.exp (-(↑↑n * ↑θ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have hden :
      ‖Complex.exp ((r : ℂ) + (r : ℂ) ^ 2 / 2)‖ =
        Real.exp (r + r ^ 2 / 2) := by
    rw [Complex.norm_exp]
    congr 1
    rw [Complex.add_re]
    have hsq : (((r : ℂ) ^ 2 / 2).re = r ^ 2 / 2) := by
      rw [Complex.div_re]
      have hre : ((r : ℂ) ^ 2).re = r ^ 2 := by
        rw [pow_two, Complex.mul_re]
        simp
        ring
      have him : ((r : ℂ) ^ 2).im = 0 := by
        rw [pow_two, Complex.mul_im]
        simp
      rw [hre, him]
      norm_num [Complex.normSq]
      ring
    rw [hsq]
    simp
  have hnum_re :
      (((r : ℂ) * Complex.exp (θ * Complex.I)) +
          ((r : ℂ) * Complex.exp (θ * Complex.I)) ^ 2 / 2).re =
        r * Real.cos θ + (r ^ 2 / 2) * Real.cos (2 * θ) := by
    have hsq_div :
        ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ 2 / 2 =
          (((r ^ 2 / 2 : ℝ) : ℂ) * Complex.exp ((2 * θ : ℝ) * Complex.I)) := by
      have hsq0 :
          ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) ^ 2 =
            ((r ^ 2 : ℝ) : ℂ) * Complex.exp ((2 * θ : ℝ) * Complex.I) := by
        rw [mul_pow, ← Complex.exp_nat_mul]
        rw [show (r : ℂ) ^ 2 = ((r ^ 2 : ℝ) : ℂ) by norm_num]
        rw [show (((2 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I)) =
            ((2 * θ : ℝ) : ℂ) * Complex.I by
          simpa using complex_two_mul_theta_I θ]
      rw [hsq0]
      norm_num [Complex.ofReal_mul]
      ring_nf
    rw [hsq_div]
    have hre1 :
        ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).re = r * Real.cos θ := by
      rw [Complex.exp_ofReal_mul_I]
      simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
    have hre2 :
        ((((r ^ 2 / 2 : ℝ) : ℂ) * Complex.exp ((2 * θ : ℝ) * Complex.I)).re =
          (r ^ 2 / 2) * Real.cos (2 * θ)) := by
      rw [Complex.exp_ofReal_mul_I]
      simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
    rw [Complex.add_re, hre1, hre2]
  have hnum :
      ‖Complex.exp (((r : ℂ) * Complex.exp (↑θ * Complex.I)) +
          ((r : ℂ) * Complex.exp (↑θ * Complex.I)) ^ 2 / 2)‖ =
        Real.exp (r * Real.cos θ + (r ^ 2 / 2) * Real.cos (2 * θ)) := by
    rw [Complex.norm_exp, hnum_re]
  have hden_pos : 0 < Real.exp (r + r ^ 2 / 2) := Real.exp_pos _
  calc
    ‖Complex.exp (((r : ℂ) * Complex.exp (↑θ * Complex.I)) +
          ((r : ℂ) * Complex.exp (↑θ * Complex.I)) ^ 2 / 2) /
        Complex.exp ((r : ℂ) + (r : ℂ) ^ 2 / 2) *
        Complex.exp (-(↑↑n * ↑θ) * Complex.I)‖
        = Real.exp (r * Real.cos θ + (r ^ 2 / 2) * Real.cos (2 * θ)) /
            Real.exp (r + r ^ 2 / 2) := by
          rw [norm_mul, hphase, mul_one, norm_div, hnum, hden]
    _ = Real.exp (r * (Real.cos θ - 1) +
          (r ^ 2 / 2) * (Real.cos (2 * θ) - 1)) := by
      rw [← Real.exp_sub]
      congr 1
      ring_nf

def involTailE (r : ℝ) : ℝ :=
  Real.exp (-(1 / (2 * Real.pi ^ 2)) * r ^ (1 / 4 : ℝ))

lemma involTailE_nonneg_eventually :
    ∀ᶠ r : ℝ in atTop, 0 ≤ involTailE r :=
  Eventually.of_forall fun r => by
    unfold involTailE
    positivity

lemma involTailE_decay :
    Tendsto (fun r : ℝ => Real.sqrt (2 * Real.pi * involSaddleBReal r) * involTailE r)
      atTop (𝓝 0) := by
  let c : ℝ := 1 / (2 * Real.pi ^ 2)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hbase :
      Tendsto (fun y : ℝ => y ^ (4 : ℝ) * Real.exp (-c * y)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (4 : ℝ) c hc
  have hy : Tendsto (fun r : ℝ => r ^ (1 / 4 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)
  have hcomp :
      Tendsto (fun r : ℝ => (r ^ (1 / 4 : ℝ)) ^ (4 : ℝ) *
        Real.exp (-c * r ^ (1 / 4 : ℝ))) atTop (𝓝 0) :=
    hbase.comp hy
  have hscaled :
      Tendsto (fun r : ℝ => Real.sqrt (6 * Real.pi) *
        ((r ^ (1 / 4 : ℝ)) ^ (4 : ℝ) *
          Real.exp (-c * r ^ (1 / 4 : ℝ)))) atTop (𝓝 0) := by
    simpa using hcomp.const_mul (Real.sqrt (6 * Real.pi))
  refine squeeze_zero' ?_ ?_ hscaled
  · exact Eventually.of_forall fun r => by
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    have hr0 : 0 ≤ r := le_trans zero_le_one hr
    have hB_le : involSaddleBReal r ≤ 3 * r ^ 2 := by
      unfold involSaddleBReal
      nlinarith [hr]
    have hsqrt :
        Real.sqrt (2 * Real.pi * involSaddleBReal r) ≤
          Real.sqrt (6 * Real.pi) * r := by
      have hmul : 2 * Real.pi * involSaddleBReal r ≤ 6 * Real.pi * r ^ 2 := by
        calc
          2 * Real.pi * involSaddleBReal r
              ≤ 2 * Real.pi * (3 * r ^ 2) :=
                mul_le_mul_of_nonneg_left hB_le (by positivity)
          _ = 6 * Real.pi * r ^ 2 := by ring_nf
      calc
        Real.sqrt (2 * Real.pi * involSaddleBReal r)
            ≤ Real.sqrt (6 * Real.pi * r ^ 2) := Real.sqrt_le_sqrt hmul
        _ = Real.sqrt (6 * Real.pi) * r := by
          have h6pi : 0 ≤ 6 * Real.pi := by positivity
          rw [Real.sqrt_mul h6pi (r ^ 2)]
          rw [Real.sqrt_sq hr0]
    have hrpow4 : (r ^ (1 / 4 : ℝ)) ^ (4 : ℝ) = r := by
      rw [← Real.rpow_mul hr0,
        show (1 / 4 : ℝ) * 4 = 1 by norm_num, Real.rpow_one]
    calc
      Real.sqrt (2 * Real.pi * involSaddleBReal r) * involTailE r
          ≤ (Real.sqrt (6 * Real.pi) * r) * involTailE r :=
            mul_le_mul_of_nonneg_right hsqrt (by
              unfold involTailE
              positivity)
      _ = Real.sqrt (6 * Real.pi) *
            ((r ^ (1 / 4 : ℝ)) ^ (4 : ℝ) *
              Real.exp (-c * r ^ (1 / 4 : ℝ))) := by
        unfold involTailE
        dsimp [c]
        rw [hrpow4]
        ring_nf

lemma invol_tail_bound_eventually :
    ∀ᶠ r : ℝ in atTop, ∀ n : ℕ, ∀ θ : ℝ,
      involSaddleDeltaReal r ≤ |θ| → |θ| ≤ Real.pi →
        ‖saddleGAt involFun r n θ‖ ≤ involTailE r := by
  let c : ℝ := 1 / (2 * Real.pi ^ 2)
  have hcpos : 0 < c := by
    dsimp [c]
    positivity
  have hc_le_one : c ≤ 1 := by
    dsimp [c]
    have hden : 1 ≤ 2 * Real.pi ^ 2 := by
      nlinarith [Real.two_le_pi]
    have hden_pos : 0 < 2 * Real.pi ^ 2 := by positivity
    rw [div_le_iff₀ hden_pos]
    nlinarith
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr n θ hδθ hθπ
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hδ0 : 0 ≤ involSaddleDeltaReal r := by
    unfold involSaddleDeltaReal
    positivity
  rw [invol_saddleGAt_norm]
  unfold involTailE
  apply Real.exp_le_exp.mpr
  have htarget_quarter : c * r ^ (1 / 4 : ℝ) ≤ r := by
    have hpow_le : r ^ (1 / 4 : ℝ) ≤ r := by
      calc
        r ^ (1 / 4 : ℝ) ≤ r ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hr (by norm_num : (1 / 4 : ℝ) ≤ 1)
        _ = r := by rw [Real.rpow_one]
    calc
      c * r ^ (1 / 4 : ℝ) ≤ 1 * r ^ (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right hc_le_one (Real.rpow_nonneg hr0 _)
      _ ≤ r := by simpa using hpow_le
  by_cases hsmall : |θ| ≤ Real.pi / 2
  · have h2θπ : |2 * θ| ≤ Real.pi := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    have hcos2 := Real.cos_le_one_sub_mul_cos_sq h2θπ
    have hcos2_sub : Real.cos (2 * θ) - 1 ≤
        -(2 / Real.pi ^ 2) * (2 * θ) ^ 2 := by
      linarith
    have hquad :
        r ^ 2 * (involSaddleDeltaReal r) ^ 2 = r ^ (1 / 2 : ℝ) := by
      have hr2_rpow : r ^ 2 = r ^ (2 : ℝ) := by
        exact (Real.rpow_natCast r 2).symm
      have hdelta_pow :
          (r ^ (-(3 / 4 : ℝ))) ^ 2 = r ^ (-(3 / 4 : ℝ) * (2 : ℝ)) :=
        (Real.rpow_mul_natCast hr0 (-(3 / 4 : ℝ)) 2).symm
      unfold involSaddleDeltaReal
      calc
        r ^ 2 * (r ^ (-(3 / 4 : ℝ))) ^ 2
            = r ^ (2 : ℝ) * r ^ (-(3 / 4 : ℝ) * (2 : ℝ)) := by
              rw [hr2_rpow, hdelta_pow]
        _ = r ^ ((2 : ℝ) + (-(3 / 4 : ℝ) * (2 : ℝ))) := by
              rw [Real.rpow_add (lt_of_lt_of_le zero_lt_one hr)]
        _ = r ^ (1 / 2 : ℝ) := by norm_num
    have hθsq : (involSaddleDeltaReal r) ^ 2 ≤ θ ^ 2 := by
      calc
        (involSaddleDeltaReal r) ^ 2 ≤ |θ| ^ 2 :=
          pow_le_pow_left₀ hδ0 hδθ 2
        _ = θ ^ 2 := by rw [sq_abs]
    have hmain :
        r * (Real.cos θ - 1) + (r ^ 2 / 2) * (Real.cos (2 * θ) - 1)
          ≤ -c * r ^ (1 / 4 : ℝ) := by
      have hcos1_nonpos : Real.cos θ - 1 ≤ 0 := by
        linarith [Real.cos_le_one θ]
      have hleft_nonpos : r * (Real.cos θ - 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hr0 hcos1_nonpos
      have hcoef_nonpos : -(4 / Real.pi ^ 2) ≤ 0 := by
        have hpos : 0 ≤ 4 / Real.pi ^ 2 := by positivity
        linarith
      have hquad_lower : r ^ (1 / 4 : ℝ) ≤ r ^ (1 / 2 : ℝ) := by
        exact Real.rpow_le_rpow_of_exponent_le hr (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)
      have hstrong :
          (r ^ 2 / 2) * (Real.cos (2 * θ) - 1)
            ≤ -(4 / Real.pi ^ 2) * (r ^ 2 * (involSaddleDeltaReal r) ^ 2) := by
        calc
          (r ^ 2 / 2) * (Real.cos (2 * θ) - 1)
              ≤ (r ^ 2 / 2) * (-(2 / Real.pi ^ 2) * (2 * θ) ^ 2) :=
                mul_le_mul_of_nonneg_left hcos2_sub (by positivity)
          _ = -(4 / Real.pi ^ 2) * (r ^ 2 * θ ^ 2) := by ring_nf
          _ ≤ -(4 / Real.pi ^ 2) * (r ^ 2 * (involSaddleDeltaReal r) ^ 2) := by
            exact mul_le_mul_of_nonpos_left
              (mul_le_mul_of_nonneg_left hθsq (sq_nonneg r)) hcoef_nonpos
      have hconst : c * r ^ (1 / 4 : ℝ) ≤
          (4 / Real.pi ^ 2) * (r ^ 2 * (involSaddleDeltaReal r) ^ 2) := by
        rw [hquad]
        have hc4 : c ≤ 4 / Real.pi ^ 2 := by
          dsimp [c]
          field_simp [Real.pi_ne_zero]
          norm_num
        calc
          c * r ^ (1 / 4 : ℝ) ≤ c * r ^ (1 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_left hquad_lower hcpos.le
          _ ≤ (4 / Real.pi ^ 2) * r ^ (1 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_right hc4 (Real.rpow_nonneg hr0 _)
      calc
        r * (Real.cos θ - 1) + (r ^ 2 / 2) * (Real.cos (2 * θ) - 1)
            ≤ 0 + (-(4 / Real.pi ^ 2) *
                (r ^ 2 * (involSaddleDeltaReal r) ^ 2)) :=
              add_le_add hleft_nonpos hstrong
        _ ≤ -c * r ^ (1 / 4 : ℝ) := by linarith
    exact hmain
  · have hlarge : Real.pi / 2 < |θ| := lt_of_not_ge hsmall
    have hcos_nonpos : Real.cos θ ≤ 0 := by
      by_cases hθnonneg : 0 ≤ θ
      · have hθ_le_pi : θ ≤ Real.pi := (abs_le.mp hθπ).2
        have hpi2_le : Real.pi / 2 ≤ θ := by
          have habs_eq : |θ| = θ := abs_of_nonneg hθnonneg
          linarith
        exact Real.cos_nonpos_of_pi_div_two_le_of_le hpi2_le (by linarith [hθ_le_pi])
      · have hθneg : θ < 0 := lt_of_not_ge hθnonneg
        have hneg_le_pi : -θ ≤ Real.pi := by
          have h := (abs_le.mp hθπ).1
          linarith
        have hpi2_le_neg : Real.pi / 2 ≤ -θ := by
          have habs_eq : |θ| = -θ := abs_of_neg hθneg
          linarith
        have hcos := Real.cos_nonpos_of_pi_div_two_le_of_le hpi2_le_neg
          (by linarith [hneg_le_pi])
        simpa [Real.cos_neg] using hcos
    have hcos2_nonpos : Real.cos (2 * θ) - 1 ≤ 0 := by
      linarith [Real.cos_le_one (2 * θ)]
    have hmain :
        r * (Real.cos θ - 1) + (r ^ 2 / 2) * (Real.cos (2 * θ) - 1)
          ≤ -c * r ^ (1 / 4 : ℝ) := by
      have hfirst : r * (Real.cos θ - 1) ≤ -r := by
        have hcos_sub : Real.cos θ - 1 ≤ -1 := by linarith
        calc
          r * (Real.cos θ - 1) ≤ r * (-1) :=
            mul_le_mul_of_nonneg_left hcos_sub hr0
          _ = -r := by ring
      have hsecond : (r ^ 2 / 2) * (Real.cos (2 * θ) - 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hcos2_nonpos
      calc
        r * (Real.cos θ - 1) + (r ^ 2 / 2) * (Real.cos (2 * θ) - 1)
            ≤ -r + 0 := add_le_add hfirst hsecond
        _ ≤ -c * r ^ (1 / 4 : ℝ) := by linarith
    exact hmain

lemma invol_tail_uniform :
    ∃ E : ℝ → ℝ,
      (∀ᶠ (r : ℝ) in atTop, 0 ≤ E r) ∧
      Tendsto (fun r : ℝ => Real.sqrt (2 * Real.pi * involSaddleBReal r) * E r)
        atTop (𝓝 0) ∧
      (∀ᶠ (r : ℝ) in atTop, ∀ n : ℕ, ∀ θ : ℝ,
        involSaddleDeltaReal r ≤ |θ| → |θ| ≤ Real.pi →
          ‖saddleGAt involFun r n θ‖ ≤ E r) := by
  exact ⟨involTailE, involTailE_nonneg_eventually, involTailE_decay, invol_tail_bound_eventually⟩

lemma involSaddleRadius_nonneg (n : ℕ) : 0 ≤ involSaddleRadius n := by
  unfold involSaddleRadius
  have hle : 1 ≤ Real.sqrt (1 + 4 * (n : ℝ)) := by
    have hn0 : 0 ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
    have hle' : Real.sqrt (1 : ℝ) ≤ Real.sqrt (1 + 4 * (n : ℝ)) :=
      Real.sqrt_le_sqrt (by nlinarith)
    simpa only [Real.sqrt_one] using hle'
  linarith

lemma involSaddleAReal_radius (n : ℕ) :
    involSaddleAReal (involSaddleRadius n) = (n : ℝ) := by
  unfold involSaddleAReal involSaddleRadius
  have hnonneg : 0 ≤ 1 + 4 * (n : ℝ) := by positivity
  have hs : Real.sqrt (1 + 4 * (n : ℝ)) ^ 2 = 1 + 4 * (n : ℝ) :=
    Real.sq_sqrt hnonneg
  nlinarith

lemma involSaddleAReal_strictMonoOn_nonneg :
    StrictMonoOn involSaddleAReal (Set.Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  unfold involSaddleAReal
  have hpos : 0 < (y - x) * (1 + x + y) := by
    have hdiff : 0 < y - x := sub_pos.mpr hxy
    have hx0 : 0 ≤ x := hx
    have hy0 : 0 ≤ y := hy
    have hsum : 0 < 1 + x + y := by linarith
    exact mul_pos hdiff hsum
  nlinarith

lemma involSaddleRadius_tendsto_atTop :
    Tendsto involSaddleRadius atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro M
  let M0 : ℝ := max M 0
  obtain ⟨N, hN⟩ := exists_nat_gt (involSaddleAReal M0)
  refine ⟨N, fun n hn => ?_⟩
  have hM0_nonneg : 0 ≤ M0 := le_max_right _ _
  have hM_le_M0 : M ≤ M0 := le_max_left _ _
  have hnR : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hAM0_lt_n : involSaddleAReal M0 < (n : ℝ) := hN.trans_le hnR
  by_contra hnot
  have hr_lt_M : involSaddleRadius n < M := lt_of_not_ge hnot
  have hr_lt_M0 : involSaddleRadius n < M0 := hr_lt_M.trans_le hM_le_M0
  have hstrict :
      involSaddleAReal (involSaddleRadius n) < involSaddleAReal M0 :=
    involSaddleAReal_strictMonoOn_nonneg
      (involSaddleRadius_nonneg n) hM0_nonneg hr_lt_M0
  rw [involSaddleAReal_radius] at hstrict
  linarith

def involHAdmissible : HAdmissible involFun involSeries where
  ρ := involSeries.radius
  radFilter := atTop
  a := involSaddleAReal
  b := involSaddleBReal
  δ := involSaddleDeltaReal
  hp := involFun_hasFPowerSeriesAt_zero
  radius_eq := rfl
  radius_pos := by
    simpa [involSeries] using involFun_hasFPowerSeriesAt_zero.radius_pos
  rad_neBot := by infer_instance
  r_pos := eventually_gt_atTop (0 : ℝ)
  differentiableOn := invol_differentiableOn_eventually
  f_pos := invol_f_pos_eventually
  b_pos := invol_b_pos_eventually
  δ_pos := invol_delta_pos_eventually
  δ_le_pi := invol_delta_le_pi_eventually
  δ_sqrt_b_tendsto_atTop := invol_delta_sqrt_b_tendsto_atTop
  local_uniform := invol_local_uniform
  tail_uniform := invol_tail_uniform

def involHAdmissibleSaddleSequence : SaddleSequence involHAdmissible where
  r := involSaddleRadius
  tendsTo := by
    simpa [involHAdmissible] using involSaddleRadius_tendsto_atTop
  saddle_eq := by
    exact Eventually.of_forall fun n => by
      change involSaddleAReal (involSaddleRadius n) = (n : ℝ)
      exact involSaddleAReal_radius n

theorem invol_coeff_isEquivalent_saddle_from_HAdmissible :
    (fun n : ℕ => involSeries.coeff n) ~[atTop]
      (fun n : ℕ => saddleScale involFun involSaddleRadius
        (fun n => involSaddleBReal (involSaddleRadius n)) n) := by
  have h := coeff_isEquivalent_saddle involHAdmissible involHAdmissibleSaddleSequence
  simpa [HAdmissible.B, involHAdmissibleSaddleSequence, involHAdmissible] using h

theorem involution_count_over_factorial_isEquivalent_saddle :
    (fun n : ℕ =>
      (((AnalyticCombinatorics.Ch1.CombClass.parts12.set.counts n : ℝ) / n.factorial : ℝ) : ℂ))
      ~[atTop]
      (fun n : ℕ => saddleScale involFun involSaddleRadius
        (fun n => involSaddleBReal (involSaddleRadius n)) n) := by
  simpa [involSeries, PowerSeries.coeff_toFMLS, involCarrier_coeff, involCoeffR] using
    invol_coeff_isEquivalent_saddle_from_HAdmissible

end InvolutionHAdmissible
end

/-!
# Involutions: the classical Moser–Wyman real saddle asymptotic

`involution_count_over_factorial_isEquivalent_saddle` (InvolutionHAdmissible) gives the abstract
H-admissible saddle estimate for the number of involutions `I_n = parts12.set.counts n` (permutations
with all cycles of length 1 or 2; EGF `exp(z + z²/2)`).  This file realifies the abstract scale to the
recognizable Moser–Wyman formula

  `I_n / n! ~ exp(r_n + r_n²/2) / ( r_n^n · √(2π · (r_n + 2 r_n²)) )`,   `r_n + r_n² = n`,

with `r_n = (√(1+4n) − 1)/2`.  "Unfold and realify" of `saddleScale`, mirroring `BellRealSaddle`.
-/

noncomputable section

open Filter Asymptotics
open scoped Topology Real

namespace InvolutionHAdmissible

/-- The saddle radius is strictly positive for `n ≥ 1`. -/
lemma involSaddleRadius_pos_of_pos {n : ℕ} (hn : 0 < n) : 0 < involSaddleRadius n := by
  have hrnn : 0 ≤ involSaddleRadius n := involSaddleRadius_nonneg n
  have hA : involSaddleAReal (involSaddleRadius n) = (n : ℝ) := involSaddleAReal_radius n
  rcases hrnn.lt_or_eq with h | h
  · exact h
  · exfalso
    rw [← h] at hA
    simp only [involSaddleAReal] at hA
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [← hA] at hnR
    simp at hnR

/-- The involution variance factor at the saddle is positive for `n ≥ 1`. -/
lemma involSaddleBReal_radius_pos_of_pos {n : ℕ} (hn : 0 < n) :
    0 < involSaddleBReal (involSaddleRadius n) := by
  have hr : 0 < involSaddleRadius n := involSaddleRadius_pos_of_pos hn
  unfold involSaddleBReal
  positivity

/-- The involution EGF is real on real input. -/
lemma involFun_real_on_real (r : ℝ) :
    involFun (r : ℂ) = (Real.exp (r + r ^ 2 / 2) : ℂ) := by
  unfold involFun
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- **Realification** of the abstract saddle scale to the Moser–Wyman real scale (`n ≥ 1`). -/
lemma invol_saddleScale_eq_ofReal_real_saddle {n : ℕ} (hn : 0 < n) :
    saddleScale involFun involSaddleRadius
        (fun n => involSaddleBReal (involSaddleRadius n)) n
      = (involRealSaddleScale n : ℂ) := by
  have hr : 0 < involSaddleRadius n := involSaddleRadius_pos_of_pos hn
  have hB : 0 < involSaddleBReal (involSaddleRadius n) := involSaddleBReal_radius_pos_of_pos hn
  have hsqrt : 0 < Real.sqrt (2 * Real.pi * involSaddleBReal (involSaddleRadius n)) :=
    Real.sqrt_pos.mpr (by positivity)
  unfold involRealSaddleScale saddleScale saddlePref saddlePrefAt
  rw [involFun_real_on_real]
  have hrC : ((involSaddleRadius n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hsqrtC :
      ((Real.sqrt (2 * Real.pi * involSaddleBReal (involSaddleRadius n)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hsqrt.ne'
  rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow]
  field_simp

/-- Eventual equality of the abstract complex scale and the real Moser–Wyman scale. -/
lemma invol_saddleScale_eventually_eq_ofReal_real_saddle :
    (fun n : ℕ =>
      saddleScale involFun involSaddleRadius
        (fun n => involSaddleBReal (involSaddleRadius n)) n)
      =ᶠ[atTop] (fun n : ℕ => (involRealSaddleScale n : ℂ)) := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact invol_saddleScale_eq_ofReal_real_saddle (by omega : 0 < n)

end InvolutionHAdmissible
end

open InvolutionHAdmissible
open Filter Asymptotics
open scoped Topology Real
theorem solution :
    (fun n : ℕ => involCoeffR n) ~[atTop] involRealSaddleScale := by
  rw [← ofReal_isEquivalent_iff]
  exact involution_count_over_factorial_isEquivalent_saddle.congr_right
    invol_saddleScale_eventually_eq_ofReal_real_saddle
