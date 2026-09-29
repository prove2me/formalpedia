-- Prove2me | solution 1 for mme_stothers_corrected_global_rate_algebra
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T15:18:03.361541+00:00
-- url     : https://prove2.me/submissions/4f77a23c-116b-4d5c-8843-0ec004b40bf6

import Definitions.Def_mme_stothers_corrected_global_rate
import Mathlib.Tactic.Ring

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true

namespace MME.StothersFourth.CorrectedRateAlgebra

private theorem entropy_factor
    (a b : Fin 10 → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    (∏ i, (Real.rpow (b i) (b i) * Real.rpow (a i) (-a i)) ^
      classMultiplicity i) = entropyProduct b / entropyProduct a := by
  have hterm : ∀ i : Fin 10,
      (Real.rpow (b i) (b i) * Real.rpow (a i) (-a i)) ^
          classMultiplicity i =
        Real.rpow (b i) ((classMultiplicity i : ℝ) * b i) *
          (Real.rpow (a i) ((classMultiplicity i : ℝ) * a i))⁻¹ := by
    intro i
    rw [mul_pow]
    have hbpow : (Real.rpow (b i) (b i)) ^ classMultiplicity i =
        Real.rpow (b i) (b i * (classMultiplicity i : ℝ)) :=
      (Real.rpow_mul_natCast (hb i) (b i) (classMultiplicity i)).symm
    have hapow : (Real.rpow (a i) (-a i)) ^ classMultiplicity i =
        Real.rpow (a i) (-a i * (classMultiplicity i : ℝ)) :=
      (Real.rpow_mul_natCast (ha i) (-a i) (classMultiplicity i)).symm
    rw [hbpow, hapow]
    rw [show b i * (classMultiplicity i : ℝ) =
      (classMultiplicity i : ℝ) * b i by ring]
    rw [show -a i * (classMultiplicity i : ℝ) =
      -((classMultiplicity i : ℝ) * a i) by ring]
    congr 1
    exact Real.rpow_neg (ha i) _
  simp_rw [hterm]
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  rfl

private theorem factorization
    (v a b : Fin 10 → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    (∏ i, (v i * Real.rpow (b i) (b i) * Real.rpow (a i) (-a i)) ^
      classMultiplicity i) =
        (∏ i, (v i) ^ classMultiplicity i) *
          (entropyProduct b / entropyProduct a) := by
  simp_rw [mul_assoc, mul_pow]
  rw [Finset.prod_mul_distrib]
  congr 1
  simpa only [mul_pow] using entropy_factor a b ha hb

end MME.StothersFourth.CorrectedRateAlgebra

open MME.StothersFourth

/-- Both rate formulas have the same constituent and marginal factors;
their entropy factors are reciprocal.  They agree on every diagonal profile. -/
theorem solution
    (q : ℕ) (tau : ℝ) (a b : Fin 10 → ℝ)
    (ha : ∀ i : Fin 10, 0 ≤ a i)
    (hb : ∀ i : Fin 10, 0 ≤ b i) :
    correctedGlobalRate q tau a b =
        (∏ i, (Real.rpow (classValue q tau i) (a i / 3)) ^
          classMultiplicity i) *
        (entropyProduct b / entropyProduct a) *
        (∏ j, Real.rpow (marginal a j) (-marginal a j)) ∧
      globalRate q tau a b =
        (∏ i, (Real.rpow (classValue q tau i) (a i / 3)) ^
          classMultiplicity i) *
        (entropyProduct a / entropyProduct b) *
        (∏ j, Real.rpow (marginal a j) (-marginal a j)) ∧
      correctedGlobalRate q tau a a = globalRate q tau a a := by
  refine ⟨?_, ?_, rfl⟩
  · unfold correctedGlobalRate
    rw [CorrectedRateAlgebra.factorization
      (fun i ↦ Real.rpow (classValue q tau i) (a i / 3)) a b ha hb]
  · unfold globalRate
    rw [CorrectedRateAlgebra.factorization
      (fun i ↦ Real.rpow (classValue q tau i) (a i / 3)) b a hb ha]
