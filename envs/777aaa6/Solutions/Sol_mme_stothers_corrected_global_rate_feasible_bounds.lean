-- Prove2me | solution 1 for mme_stothers_corrected_global_rate_feasible_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T15:25:07.948669+00:00
-- url     : https://prove2.me/submissions/233d03ba-4623-4f0c-a21d-d89bdaebc076

import Definitions.Def_mme_stothers_corrected_global_rate
import Theorems.Thm_mme_stothers_corrected_global_rate_algebra
import Theorems.Thm_mme_stothers_lemma52_same_marginal
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true

namespace MME.StothersFourth.CorrectedRateBounds

private theorem classValue_pos
    (q : ℕ) (hq : 0 < q) (tau : ℝ) (i : Fin 10) :
    0 < classValue q tau i := by
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  fin_cases i <;> dsimp [classValue, E, H, L] <;> positivity

private theorem marginal_pos
    (a : Fin 10 → ℝ) (haPos : ∀ i, 0 < a i) (j : Fin 9) :
    0 < marginal a j := by
  have h0 := haPos 0
  have h1 := haPos 1
  have h2 := haPos 2
  have h3 := haPos 3
  have h4 := haPos 4
  have h5 := haPos 5
  have h6 := haPos 6
  have h7 := haPos 7
  have h8 := haPos 8
  have h9 := haPos 9
  fin_cases j <;> dsimp [marginal, Q] <;> positivity

private theorem entropyProduct_pos
    (a : Fin 10 → ℝ) (haPos : ∀ i, 0 < a i) :
    0 < entropyProduct a := by
  unfold entropyProduct
  exact Finset.prod_pos fun i _ ↦ Real.rpow_pos_of_pos (haPos i) _

end MME.StothersFourth.CorrectedRateBounds

open MME.StothersFourth

/-- Every positive feasible pair gives a positive corrected rate, and the
corrected rate is bounded above by the old reciprocal-factor formula. -/
theorem solution
    (q : ℕ) (hq : 0 < q) (tau : ℝ) (a b : Fin 10 → ℝ)
    (ha : InZ a) (hb : InN b)
    (haPos : ∀ i : Fin 10, 0 < a i)
    (hbPos : ∀ i : Fin 10, 0 < b i)
    (hsame : InY (fun i ↦ a i - b i)) :
    0 < correctedGlobalRate q tau a b ∧
      correctedGlobalRate q tau a b ≤ globalRate q tau a b := by
  let C : ℝ := ∏ i,
    (Real.rpow (classValue q tau i) (a i / 3)) ^ classMultiplicity i
  let M : ℝ := ∏ j, Real.rpow (marginal a j) (-marginal a j)
  have hC : 0 < C := by
    apply Finset.prod_pos
    intro i _
    exact pow_pos
      (Real.rpow_pos_of_pos (CorrectedRateBounds.classValue_pos q hq tau i) _)
      _
  have hM : 0 < M := by
    apply Finset.prod_pos
    intro j _
    exact Real.rpow_pos_of_pos (CorrectedRateBounds.marginal_pos a haPos j) _
  have hA : 0 < entropyProduct a := CorrectedRateBounds.entropyProduct_pos a haPos
  have hB : 0 < entropyProduct b := CorrectedRateBounds.entropyProduct_pos b hbPos
  have hBA : entropyProduct b ≤ entropyProduct a :=
    mme_stothers_lemma52_same_marginal.2 a b ha hb hbPos hsame
  have hratio : entropyProduct b / entropyProduct a ≤
      entropyProduct a / entropyProduct b :=
    ((div_le_one hA).mpr hBA).trans ((one_le_div hB).mpr hBA)
  rcases mme_stothers_corrected_global_rate_algebra q tau a b
      (fun i ↦ (haPos i).le) (fun i ↦ (hbPos i).le) with
    ⟨hcorrected, hold, _⟩
  change correctedGlobalRate q tau a b =
    C * (entropyProduct b / entropyProduct a) * M at hcorrected
  change globalRate q tau a b =
    C * (entropyProduct a / entropyProduct b) * M at hold
  rw [hcorrected, hold]
  exact ⟨mul_pos (mul_pos hC (div_pos hB hA)) hM,
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hratio hC.le) hM.le⟩
