-- Prove2me | solution 1 for mme_released_interior_422_owner3_region2_coarse_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T07:19:10.956293+00:00
-- url     : https://prove2.me/submissions/0ab2901c-4550-47d4-8bf2-e9fcd3f1fbf1

import Theorems.Thm_mme_rational_coarse_penalty_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.RecursiveThinSplit MME.ReleasedInterior

private def alphaQ (c : MME.ReleasedInterior.Split 32) : ℚ :=
  (splitWeight 3 32 2 c : ℚ) / 1000000000000

private def jointExponent (c : MME.ReleasedInterior.Split 32) : ℕ :=
  [3, 5, 12, 5, 1, 5, 12, 5, 3].getD ((seed 3 32).splits.idxOf (sourceShape 3 c)) 0

/-- The smallest audited regional coarse margin is positive for the actual
released split distribution, with every arithmetic check performed in Lean. -/
theorem solution :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 32 => c.val 0)
        (fun c => (splitWeight 3 32 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 32 => (splitWeight 3 32 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 32) : 0 ≤ alphaQ c := by
    unfold alphaQ
    positivity
  have hprob : ∑ c, alphaQ c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![335954784,79859110825,839609875420,79859158060,335900911] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![181883563693,636232827833,181883608474,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![12,4,0,4,12] ![12,4,0,4,12] ![3,1,3,40,40] jointExponent (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 32 => c.val 0)
        (fun c => (alphaQ c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc


#print axioms solution
