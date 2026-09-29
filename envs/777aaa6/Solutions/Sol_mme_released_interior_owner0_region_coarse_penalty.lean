-- Prove2me | solution 1 for mme_released_interior_owner0_region_coarse_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T07:19:11.504775+00:00
-- url     : https://prove2.me/submissions/f0089bd6-410a-48cb-99a4-e8a6bead8c57

import Theorems.Thm_mme_rational_coarse_penalty_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.RecursiveThinSplit MME.ReleasedInterior

private def alphaQ_s10_r0 (c : MME.ReleasedInterior.Split 10) : ℚ :=
  (splitWeight 0 10 0 c : ℚ) / 1000000000000

private def jointExponent_s10_r0 (c : MME.ReleasedInterior.Split 10) : ℕ :=
  [3, 1, 1, 3].getD ((seed 0 10).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s10_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 10 => c.val 0)
        (fun c => (splitWeight 0 10 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 10 => (splitWeight 0 10 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 10) : 0 ≤ alphaQ_s10_r0 c := by
    unfold alphaQ_s10_r0
    positivity
  have hprob : ∑ c, alphaQ_s10_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999237731,500000762269,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000021543,499999978457,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s10_r0 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![1,1,0,0,0] ![1,1,40,40,40] ![1,1,40,40,40] jointExponent_s10_r0 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 10 => c.val 0)
        (fun c => (alphaQ_s10_r0 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s10_r0 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s10_r0, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s10_r1 (c : MME.ReleasedInterior.Split 10) : ℚ :=
  (splitWeight 0 10 1 c : ℚ) / 1000000000000

private def jointExponent_s10_r1 (c : MME.ReleasedInterior.Split 10) : ℕ :=
  [3, 1, 1, 3].getD ((seed 0 10).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s10_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 10 => c.val 0)
        (fun c => (splitWeight 0 10 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 10 => (splitWeight 0 10 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 10) : 0 ≤ alphaQ_s10_r1 c := by
    unfold alphaQ_s10_r1
    positivity
  have hprob : ∑ c, alphaQ_s10_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999714324,500000285676,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999949344,500000050656,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s10_r1 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![1,1,0,0,0] ![1,1,40,40,40] ![1,1,40,40,40] jointExponent_s10_r1 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 10 => c.val 0)
        (fun c => (alphaQ_s10_r1 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s10_r1 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s10_r1, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s10_r2 (c : MME.ReleasedInterior.Split 10) : ℚ :=
  (splitWeight 0 10 2 c : ℚ) / 1000000000000

private def jointExponent_s10_r2 (c : MME.ReleasedInterior.Split 10) : ℕ :=
  [3, 1, 1, 3].getD ((seed 0 10).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s10_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 10 => c.val 0)
        (fun c => (splitWeight 0 10 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 10 => (splitWeight 0 10 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 10) : 0 ≤ alphaQ_s10_r2 c := by
    unfold alphaQ_s10_r2
    positivity
  have hprob : ∑ c, alphaQ_s10_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000128098,499999871902,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999456134,500000543866,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s10_r2 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![1,1,0,0,0] ![1,1,40,40,40] ![1,1,40,40,40] jointExponent_s10_r2 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 10 => c.val 0)
        (fun c => (alphaQ_s10_r2 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s10_r2 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s10_r2, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s10_r3 (c : MME.ReleasedInterior.Split 10) : ℚ :=
  (splitWeight 0 10 3 c : ℚ) / 1000000000000

private def jointExponent_s10_r3 (c : MME.ReleasedInterior.Split 10) : ℕ :=
  [3, 1, 1, 3].getD ((seed 0 10).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s10_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 10 => c.val 0)
        (fun c => (splitWeight 0 10 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 10 => (splitWeight 0 10 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 10) : 0 ≤ alphaQ_s10_r3 c := by
    unfold alphaQ_s10_r3
    positivity
  have hprob : ∑ c, alphaQ_s10_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000023341,499999976659,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999811990,500000188010,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s10_r3 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![1,1,0,0,0] ![1,1,40,40,40] ![1,1,40,40,40] jointExponent_s10_r3 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 10 => c.val 0)
        (fun c => (alphaQ_s10_r3 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s10_r3 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s10_r3, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s10_r4 (c : MME.ReleasedInterior.Split 10) : ℚ :=
  (splitWeight 0 10 4 c : ℚ) / 1000000000000

private def jointExponent_s10_r4 (c : MME.ReleasedInterior.Split 10) : ℕ :=
  [3, 1, 1, 3].getD ((seed 0 10).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s10_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 10 => c.val 0)
        (fun c => (splitWeight 0 10 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 10 => (splitWeight 0 10 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 10) : 0 ≤ alphaQ_s10_r4 c := by
    unfold alphaQ_s10_r4
    positivity
  have hprob : ∑ c, alphaQ_s10_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999870659,500000129341,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999960533,500000039467,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s10_r4 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![1,1,0,0,0] ![1,1,40,40,40] ![1,1,40,40,40] jointExponent_s10_r4 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 10 => c.val 0)
        (fun c => (alphaQ_s10_r4 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s10_r4 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s10_r4, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s10_r5 (c : MME.ReleasedInterior.Split 10) : ℚ :=
  (splitWeight 0 10 5 c : ℚ) / 1000000000000

private def jointExponent_s10_r5 (c : MME.ReleasedInterior.Split 10) : ℕ :=
  [3, 1, 1, 3].getD ((seed 0 10).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s10_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 10 => c.val 0)
        (fun c => (splitWeight 0 10 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 10 => (splitWeight 0 10 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 10) : 0 ≤ alphaQ_s10_r5 c := by
    unfold alphaQ_s10_r5
    positivity
  have hprob : ∑ c, alphaQ_s10_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000210744,499999789256,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999747056,500000252944,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s10_r5 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![1,1,0,0,0] ![1,1,40,40,40] ![1,1,40,40,40] jointExponent_s10_r5 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 10 => c.val 0)
        (fun c => (alphaQ_s10_r5 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s10_r5 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s10_r5, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s11_r0 (c : MME.ReleasedInterior.Split 11) : ℚ :=
  (splitWeight 0 11 0 c : ℚ) / 1000000000000

private def jointExponent_s11_r0 (c : MME.ReleasedInterior.Split 11) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 0 11).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s11_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 11 => c.val 0)
        (fun c => (splitWeight 0 11 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 11 => (splitWeight 0 11 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 11) : 0 ≤ alphaQ_s11_r0 c := by
    unfold alphaQ_s11_r0
    positivity
  have hprob : ∑ c, alphaQ_s11_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000013162,499999986838,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,6583538552,493416477271,493416417996,6583566181] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s11_r0 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![1,1,0,0,0] ![1,1,40,40,40] ![40,7,1,1,7] jointExponent_s11_r0 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 11 => c.val 0)
        (fun c => (alphaQ_s11_r0 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s11_r0 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s11_r0, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s11_r2 (c : MME.ReleasedInterior.Split 11) : ℚ :=
  (splitWeight 0 11 2 c : ℚ) / 1000000000000

private def jointExponent_s11_r2 (c : MME.ReleasedInterior.Split 11) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 0 11).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s11_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 11 => c.val 0)
        (fun c => (splitWeight 0 11 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 11 => (splitWeight 0 11 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 11) : 0 ≤ alphaQ_s11_r2 c := by
    unfold alphaQ_s11_r2
    positivity
  have hprob : ∑ c, alphaQ_s11_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000015647,499999984353,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,6609542672,493390474326,493390399449,6609583553] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s11_r2 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![1,1,0,0,0] ![1,1,40,40,40] ![40,7,1,1,7] jointExponent_s11_r2 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 11 => c.val 0)
        (fun c => (alphaQ_s11_r2 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s11_r2 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s11_r2, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s11_r3 (c : MME.ReleasedInterior.Split 11) : ℚ :=
  (splitWeight 0 11 3 c : ℚ) / 1000000000000

private def jointExponent_s11_r3 (c : MME.ReleasedInterior.Split 11) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 0 11).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s11_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 11 => c.val 0)
        (fun c => (splitWeight 0 11 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 11 => (splitWeight 0 11 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 11) : 0 ≤ alphaQ_s11_r3 c := by
    unfold alphaQ_s11_r3
    positivity
  have hprob : ∑ c, alphaQ_s11_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000016235,499999983765,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,6633545863,493366464666,493366418935,6633570536] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s11_r3 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![1,1,0,0,0] ![1,1,40,40,40] ![40,7,1,1,7] jointExponent_s11_r3 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 11 => c.val 0)
        (fun c => (alphaQ_s11_r3 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s11_r3 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s11_r3, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s12_r0 (c : MME.ReleasedInterior.Split 12) : ℚ :=
  (splitWeight 0 12 0 c : ℚ) / 1000000000000

private def jointExponent_s12_r0 (c : MME.ReleasedInterior.Split 12) : ℕ :=
  [12, 4, 1, 6, 6, 1, 4, 12].getD ((seed 0 12).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s12_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 12 => c.val 0)
        (fun c => (splitWeight 0 12 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 12 => (splitWeight 0 12 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 12) : 0 ≤ alphaQ_s12_r0 c := by
    unfold alphaQ_s12_r0
    positivity
  have hprob : ∑ c, alphaQ_s12_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000059769,499999940231,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![326218906,73587637807,852172316614,73587605560,326221113] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s12_r0 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![1,1,0,0,0] ![1,1,40,40,40] ![12,4,0,4,12] jointExponent_s12_r0 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 12 => c.val 0)
        (fun c => (alphaQ_s12_r0 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s12_r0 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s12_r0, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s12_r2 (c : MME.ReleasedInterior.Split 12) : ℚ :=
  (splitWeight 0 12 2 c : ℚ) / 1000000000000

private def jointExponent_s12_r2 (c : MME.ReleasedInterior.Split 12) : ℕ :=
  [12, 4, 1, 6, 6, 1, 4, 12].getD ((seed 0 12).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s12_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 12 => c.val 0)
        (fun c => (splitWeight 0 12 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 12 => (splitWeight 0 12 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 12) : 0 ≤ alphaQ_s12_r2 c := by
    unfold alphaQ_s12_r2
    positivity
  have hprob : ∑ c, alphaQ_s12_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000089500,499999910500,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![323375674,73605684894,852141922897,73605645080,323371455] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s12_r2 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![1,1,0,0,0] ![1,1,40,40,40] ![12,4,0,4,12] jointExponent_s12_r2 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 12 => c.val 0)
        (fun c => (alphaQ_s12_r2 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s12_r2 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s12_r2, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s12_r3 (c : MME.ReleasedInterior.Split 12) : ℚ :=
  (splitWeight 0 12 3 c : ℚ) / 1000000000000

private def jointExponent_s12_r3 (c : MME.ReleasedInterior.Split 12) : ℕ :=
  [12, 4, 1, 6, 6, 1, 4, 12].getD ((seed 0 12).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s12_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 12 => c.val 0)
        (fun c => (splitWeight 0 12 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 12 => (splitWeight 0 12 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 12) : 0 ≤ alphaQ_s12_r3 c := by
    unfold alphaQ_s12_r3
    positivity
  have hprob : ∑ c, alphaQ_s12_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000008199,499999991801,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![325661732,70610688508,858127310119,70610681145,325658496] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s12_r3 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![1,1,0,0,0] ![1,1,40,40,40] ![12,4,0,4,12] jointExponent_s12_r3 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 12 => c.val 0)
        (fun c => (alphaQ_s12_r3 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s12_r3 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s12_r3, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s13_r1 (c : MME.ReleasedInterior.Split 13) : ℚ :=
  (splitWeight 0 13 1 c : ℚ) / 1000000000000

private def jointExponent_s13_r1 (c : MME.ReleasedInterior.Split 13) : ℕ :=
  [6, 1, 4, 12, 12, 4, 1, 6].getD ((seed 0 13).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s13_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 13 => c.val 0)
        (fun c => (splitWeight 0 13 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 13 => (splitWeight 0 13 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 13) : 0 ≤ alphaQ_s13_r1 c := by
    unfold alphaQ_s13_r1
    positivity
  have hprob : ∑ c, alphaQ_s13_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999809201,500000190799,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![327360604,77712568106,843920034490,77712629533,327407267] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s13_r1 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![1,1,0,0,0] ![1,1,40,40,40] ![12,4,0,4,12] jointExponent_s13_r1 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 13 => c.val 0)
        (fun c => (alphaQ_s13_r1 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s13_r1 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s13_r1, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s13_r4 (c : MME.ReleasedInterior.Split 13) : ℚ :=
  (splitWeight 0 13 4 c : ℚ) / 1000000000000

private def jointExponent_s13_r4 (c : MME.ReleasedInterior.Split 13) : ℕ :=
  [6, 1, 4, 12, 12, 4, 1, 6].getD ((seed 0 13).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s13_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 13 => c.val 0)
        (fun c => (splitWeight 0 13 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 13 => (splitWeight 0 13 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 13) : 0 ≤ alphaQ_s13_r4 c := by
    unfold alphaQ_s13_r4
    positivity
  have hprob : ∑ c, alphaQ_s13_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000095370,499999904630,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![325743861,77660512861,844027545632,77660477318,325720328] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s13_r4 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![1,1,0,0,0] ![1,1,40,40,40] ![12,4,0,4,12] jointExponent_s13_r4 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 13 => c.val 0)
        (fun c => (alphaQ_s13_r4 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s13_r4 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s13_r4, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s13_r5 (c : MME.ReleasedInterior.Split 13) : ℚ :=
  (splitWeight 0 13 5 c : ℚ) / 1000000000000

private def jointExponent_s13_r5 (c : MME.ReleasedInterior.Split 13) : ℕ :=
  [6, 1, 4, 12, 12, 4, 1, 6].getD ((seed 0 13).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s13_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 13 => c.val 0)
        (fun c => (splitWeight 0 13 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 13 => (splitWeight 0 13 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 13) : 0 ≤ alphaQ_s13_r5 c := by
    unfold alphaQ_s13_r5
    positivity
  have hprob : ∑ c, alphaQ_s13_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999998246,500000001754,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![324023595,74868226512,849615523583,74868264444,323961866] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s13_r5 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![1,1,0,0,0] ![1,1,40,40,40] ![12,4,0,4,12] jointExponent_s13_r5 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 13 => c.val 0)
        (fun c => (alphaQ_s13_r5 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s13_r5 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s13_r5, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s14_r0 (c : MME.ReleasedInterior.Split 14) : ℚ :=
  (splitWeight 0 14 0 c : ℚ) / 1000000000000

private def jointExponent_s14_r0 (c : MME.ReleasedInterior.Split 14) : ℕ :=
  [3, 2, 7, 7, 2, 3].getD ((seed 0 14).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s14_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 14 => c.val 0)
        (fun c => (splitWeight 0 14 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 14 => (splitWeight 0 14 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 14) : 0 ≤ alphaQ_s14_r0 c := by
    unfold alphaQ_s14_r0
    positivity
  have hprob : ∑ c, alphaQ_s14_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000102014,499999897986,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,7158551838,492841511536,492841282078,7158654548] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s14_r0 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![1,1,0,0,0] ![1,1,40,40,40] ![40,7,1,1,7] jointExponent_s14_r0 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 14 => c.val 0)
        (fun c => (alphaQ_s14_r0 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s14_r0 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s14_r0, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s14_r1 (c : MME.ReleasedInterior.Split 14) : ℚ :=
  (splitWeight 0 14 1 c : ℚ) / 1000000000000

private def jointExponent_s14_r1 (c : MME.ReleasedInterior.Split 14) : ℕ :=
  [3, 2, 7, 7, 2, 3].getD ((seed 0 14).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s14_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 14 => c.val 0)
        (fun c => (splitWeight 0 14 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 14 => (splitWeight 0 14 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 14) : 0 ≤ alphaQ_s14_r1 c := by
    unfold alphaQ_s14_r1
    positivity
  have hprob : ∑ c, alphaQ_s14_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000046464,499999953536,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,7078698661,492921349757,492921272802,7078678780] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s14_r1 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![1,1,0,0,0] ![1,1,40,40,40] ![40,7,1,1,7] jointExponent_s14_r1 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 14 => c.val 0)
        (fun c => (alphaQ_s14_r1 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s14_r1 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s14_r1, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s14_r2 (c : MME.ReleasedInterior.Split 14) : ℚ :=
  (splitWeight 0 14 2 c : ℚ) / 1000000000000

private def jointExponent_s14_r2 (c : MME.ReleasedInterior.Split 14) : ℕ :=
  [3, 2, 7, 7, 2, 3].getD ((seed 0 14).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s14_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 14 => c.val 0)
        (fun c => (splitWeight 0 14 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 14 => (splitWeight 0 14 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 14) : 0 ≤ alphaQ_s14_r2 c := by
    unfold alphaQ_s14_r2
    positivity
  have hprob : ∑ c, alphaQ_s14_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999964230,500000035770,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,7153828398,492846301037,492846050530,7153820035] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s14_r2 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![1,1,0,0,0] ![1,1,40,40,40] ![40,7,1,1,7] jointExponent_s14_r2 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 14 => c.val 0)
        (fun c => (alphaQ_s14_r2 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s14_r2 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s14_r2, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s14_r4 (c : MME.ReleasedInterior.Split 14) : ℚ :=
  (splitWeight 0 14 4 c : ℚ) / 1000000000000

private def jointExponent_s14_r4 (c : MME.ReleasedInterior.Split 14) : ℕ :=
  [3, 2, 7, 7, 2, 3].getD ((seed 0 14).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s14_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 14 => c.val 0)
        (fun c => (splitWeight 0 14 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 14 => (splitWeight 0 14 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 14) : 0 ≤ alphaQ_s14_r4 c := by
    unfold alphaQ_s14_r4
    positivity
  have hprob : ∑ c, alphaQ_s14_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000040754,499999959246,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,7078241061,492921824721,492921729626,7078204592] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s14_r4 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![1,1,0,0,0] ![1,1,40,40,40] ![40,7,1,1,7] jointExponent_s14_r4 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 14 => c.val 0)
        (fun c => (alphaQ_s14_r4 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s14_r4 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s14_r4, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s14_r5 (c : MME.ReleasedInterior.Split 14) : ℚ :=
  (splitWeight 0 14 5 c : ℚ) / 1000000000000

private def jointExponent_s14_r5 (c : MME.ReleasedInterior.Split 14) : ℕ :=
  [3, 2, 7, 7, 2, 3].getD ((seed 0 14).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s14_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 14 => c.val 0)
        (fun c => (splitWeight 0 14 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 14 => (splitWeight 0 14 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 14) : 0 ≤ alphaQ_s14_r5 c := by
    unfold alphaQ_s14_r5
    positivity
  have hprob : ∑ c, alphaQ_s14_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000045827,499999954173,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,7040292442,492959775501,492959667780,7040264277] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s14_r5 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![1,1,0,0,0] ![1,1,40,40,40] ![40,7,1,1,7] jointExponent_s14_r5 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 14 => c.val 0)
        (fun c => (alphaQ_s14_r5 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s14_r5 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s14_r5, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s15_r0 (c : MME.ReleasedInterior.Split 15) : ℚ :=
  (splitWeight 0 15 0 c : ℚ) / 1000000000000

private def jointExponent_s15_r0 (c : MME.ReleasedInterior.Split 15) : ℕ :=
  [1, 3, 3, 1].getD ((seed 0 15).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s15_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 15 => c.val 0)
        (fun c => (splitWeight 0 15 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 15 => (splitWeight 0 15 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 15) : 0 ≤ alphaQ_s15_r0 c := by
    unfold alphaQ_s15_r0
    positivity
  have hprob : ∑ c, alphaQ_s15_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500168612015,499831387985,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500202782228,499797217772,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s15_r0 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![1,1,0,0,0] ![1,1,40,40,40] ![1,1,40,40,40] jointExponent_s15_r0 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 15 => c.val 0)
        (fun c => (alphaQ_s15_r0 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s15_r0 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s15_r0, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s15_r1 (c : MME.ReleasedInterior.Split 15) : ℚ :=
  (splitWeight 0 15 1 c : ℚ) / 1000000000000

private def jointExponent_s15_r1 (c : MME.ReleasedInterior.Split 15) : ℕ :=
  [1, 3, 3, 1].getD ((seed 0 15).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s15_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 15 => c.val 0)
        (fun c => (splitWeight 0 15 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 15 => (splitWeight 0 15 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 15) : 0 ≤ alphaQ_s15_r1 c := by
    unfold alphaQ_s15_r1
    positivity
  have hprob : ∑ c, alphaQ_s15_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500131934035,499868065965,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500159071306,499840928694,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s15_r1 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![1,1,0,0,0] ![1,1,40,40,40] ![1,1,40,40,40] jointExponent_s15_r1 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 15 => c.val 0)
        (fun c => (alphaQ_s15_r1 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s15_r1 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s15_r1, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s15_r2 (c : MME.ReleasedInterior.Split 15) : ℚ :=
  (splitWeight 0 15 2 c : ℚ) / 1000000000000

private def jointExponent_s15_r2 (c : MME.ReleasedInterior.Split 15) : ℕ :=
  [1, 3, 3, 1].getD ((seed 0 15).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s15_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 15 => c.val 0)
        (fun c => (splitWeight 0 15 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 15 => (splitWeight 0 15 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 15) : 0 ≤ alphaQ_s15_r2 c := by
    unfold alphaQ_s15_r2
    positivity
  have hprob : ∑ c, alphaQ_s15_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500175084546,499824915454,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500212072239,499787927761,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s15_r2 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![1,1,0,0,0] ![1,1,40,40,40] ![1,1,40,40,40] jointExponent_s15_r2 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 15 => c.val 0)
        (fun c => (alphaQ_s15_r2 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s15_r2 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s15_r2, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s15_r3 (c : MME.ReleasedInterior.Split 15) : ℚ :=
  (splitWeight 0 15 3 c : ℚ) / 1000000000000

private def jointExponent_s15_r3 (c : MME.ReleasedInterior.Split 15) : ℕ :=
  [1, 3, 3, 1].getD ((seed 0 15).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s15_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 15 => c.val 0)
        (fun c => (splitWeight 0 15 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 15 => (splitWeight 0 15 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 15) : 0 ≤ alphaQ_s15_r3 c := by
    unfold alphaQ_s15_r3
    positivity
  have hprob : ∑ c, alphaQ_s15_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500174788264,499825211736,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500213829253,499786170747,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s15_r3 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![1,1,0,0,0] ![1,1,40,40,40] ![1,1,40,40,40] jointExponent_s15_r3 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 15 => c.val 0)
        (fun c => (alphaQ_s15_r3 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s15_r3 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s15_r3, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s15_r4 (c : MME.ReleasedInterior.Split 15) : ℚ :=
  (splitWeight 0 15 4 c : ℚ) / 1000000000000

private def jointExponent_s15_r4 (c : MME.ReleasedInterior.Split 15) : ℕ :=
  [1, 3, 3, 1].getD ((seed 0 15).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s15_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 15 => c.val 0)
        (fun c => (splitWeight 0 15 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 15 => (splitWeight 0 15 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 15) : 0 ≤ alphaQ_s15_r4 c := by
    unfold alphaQ_s15_r4
    positivity
  have hprob : ∑ c, alphaQ_s15_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500131921707,499868078293,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500159313845,499840686155,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s15_r4 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![1,1,0,0,0] ![1,1,40,40,40] ![1,1,40,40,40] jointExponent_s15_r4 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 15 => c.val 0)
        (fun c => (alphaQ_s15_r4 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s15_r4 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s15_r4, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s15_r5 (c : MME.ReleasedInterior.Split 15) : ℚ :=
  (splitWeight 0 15 5 c : ℚ) / 1000000000000

private def jointExponent_s15_r5 (c : MME.ReleasedInterior.Split 15) : ℕ :=
  [1, 3, 3, 1].getD ((seed 0 15).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s15_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 15 => c.val 0)
        (fun c => (splitWeight 0 15 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 15 => (splitWeight 0 15 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 15) : 0 ≤ alphaQ_s15_r5 c := by
    unfold alphaQ_s15_r5
    positivity
  have hprob : ∑ c, alphaQ_s15_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500158777754,499841222246,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500192646133,499807353867,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s15_r5 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![1,1,0,0,0] ![1,1,40,40,40] ![1,1,40,40,40] jointExponent_s15_r5 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 15 => c.val 0)
        (fun c => (alphaQ_s15_r5 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s15_r5 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s15_r5, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s18_r0 (c : MME.ReleasedInterior.Split 18) : ℚ :=
  (splitWeight 0 18 0 c : ℚ) / 1000000000000

private def jointExponent_s18_r0 (c : MME.ReleasedInterior.Split 18) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 0 18).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s18_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 18 => c.val 0)
        (fun c => (splitWeight 0 18 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 18 => (splitWeight 0 18 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 18) : 0 ≤ alphaQ_s18_r0 c := by
    unfold alphaQ_s18_r0
    positivity
  have hprob : ∑ c, alphaQ_s18_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000032378,499999967622,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,6607452517,493392597629,493392301583,6607648271] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s18_r0 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![3,1,3,0,0] ![1,1,40,40,40] ![40,7,1,1,7] jointExponent_s18_r0 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 18 => c.val 0)
        (fun c => (alphaQ_s18_r0 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s18_r0 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s18_r0, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s18_r1 (c : MME.ReleasedInterior.Split 18) : ℚ :=
  (splitWeight 0 18 1 c : ℚ) / 1000000000000

private def jointExponent_s18_r1 (c : MME.ReleasedInterior.Split 18) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 0 18).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s18_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 18 => c.val 0)
        (fun c => (splitWeight 0 18 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 18 => (splitWeight 0 18 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 18) : 0 ≤ alphaQ_s18_r1 c := by
    unfold alphaQ_s18_r1
    positivity
  have hprob : ∑ c, alphaQ_s18_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000027840,499999972160,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,6630657209,493369387784,493369157271,6630797736] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s18_r1 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![3,1,3,0,0] ![1,1,40,40,40] ![40,7,1,1,7] jointExponent_s18_r1 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 18 => c.val 0)
        (fun c => (alphaQ_s18_r1 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s18_r1 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s18_r1, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s18_r2 (c : MME.ReleasedInterior.Split 18) : ℚ :=
  (splitWeight 0 18 2 c : ℚ) / 1000000000000

private def jointExponent_s18_r2 (c : MME.ReleasedInterior.Split 18) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 0 18).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s18_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 18 => c.val 0)
        (fun c => (splitWeight 0 18 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 18 => (splitWeight 0 18 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 18) : 0 ≤ alphaQ_s18_r2 c := by
    unfold alphaQ_s18_r2
    positivity
  have hprob : ∑ c, alphaQ_s18_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000022645,499999977355,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,6582447307,493417592237,493417378072,6582582384] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s18_r2 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![3,1,3,0,0] ![1,1,40,40,40] ![40,7,1,1,7] jointExponent_s18_r2 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 18 => c.val 0)
        (fun c => (alphaQ_s18_r2 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s18_r2 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s18_r2, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s19_r0 (c : MME.ReleasedInterior.Split 19) : ℚ :=
  (splitWeight 0 19 0 c : ℚ) / 1000000000000

private def jointExponent_s19_r0 (c : MME.ReleasedInterior.Split 19) : ℕ :=
  [12, 5, 3, 5, 1, 5, 3, 5, 12].getD ((seed 0 19).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s19_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 19 => c.val 0)
        (fun c => (splitWeight 0 19 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 19 => (splitWeight 0 19 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 19) : 0 ≤ alphaQ_s19_r0 c := by
    unfold alphaQ_s19_r0
    positivity
  have hprob : ∑ c, alphaQ_s19_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![183318718397,633362557243,183318724360,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![320475753,72979993128,853399063593,72980000819,320466707] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s19_r0 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![3,1,3,0,0] ![3,1,3,40,40] ![12,4,0,4,12] jointExponent_s19_r0 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 19 => c.val 0)
        (fun c => (alphaQ_s19_r0 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s19_r0 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s19_r0, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s19_r1 (c : MME.ReleasedInterior.Split 19) : ℚ :=
  (splitWeight 0 19 1 c : ℚ) / 1000000000000

private def jointExponent_s19_r1 (c : MME.ReleasedInterior.Split 19) : ℕ :=
  [12, 5, 3, 5, 1, 5, 3, 5, 12].getD ((seed 0 19).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s19_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 19 => c.val 0)
        (fun c => (splitWeight 0 19 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 19 => (splitWeight 0 19 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 19) : 0 ≤ alphaQ_s19_r1 c := by
    unfold alphaQ_s19_r1
    positivity
  have hprob : ∑ c, alphaQ_s19_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![180408131762,639183737686,180408130552,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![318630963,71751062170,855860612641,71751064434,318629792] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s19_r1 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![3,1,3,0,0] ![3,1,3,40,40] ![12,4,0,4,12] jointExponent_s19_r1 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 19 => c.val 0)
        (fun c => (alphaQ_s19_r1 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s19_r1 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s19_r1, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s19_r2 (c : MME.ReleasedInterior.Split 19) : ℚ :=
  (splitWeight 0 19 2 c : ℚ) / 1000000000000

private def jointExponent_s19_r2 (c : MME.ReleasedInterior.Split 19) : ℕ :=
  [12, 5, 3, 5, 1, 5, 3, 5, 12].getD ((seed 0 19).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s19_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 19 => c.val 0)
        (fun c => (splitWeight 0 19 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 19 => (splitWeight 0 19 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 19) : 0 ≤ alphaQ_s19_r2 c := by
    unfold alphaQ_s19_r2
    positivity
  have hprob : ∑ c, alphaQ_s19_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![183344526558,633310945148,183344528294,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![320480044,72977622577,853403796646,72977622280,320478453] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s19_r2 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![3,1,3,0,0] ![3,1,3,40,40] ![12,4,0,4,12] jointExponent_s19_r2 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 19 => c.val 0)
        (fun c => (alphaQ_s19_r2 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s19_r2 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s19_r2, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s19_r3 (c : MME.ReleasedInterior.Split 19) : ℚ :=
  (splitWeight 0 19 3 c : ℚ) / 1000000000000

private def jointExponent_s19_r3 (c : MME.ReleasedInterior.Split 19) : ℕ :=
  [12, 5, 3, 5, 1, 5, 3, 5, 12].getD ((seed 0 19).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s19_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 19 => c.val 0)
        (fun c => (splitWeight 0 19 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 19 => (splitWeight 0 19 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 19) : 0 ≤ alphaQ_s19_r3 c := by
    unfold alphaQ_s19_r3
    positivity
  have hprob : ∑ c, alphaQ_s19_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![180451892336,639096216762,180451890902,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![318768359,71759442807,855843574162,71759448692,318765980] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s19_r3 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![3,1,3,0,0] ![3,1,3,40,40] ![12,4,0,4,12] jointExponent_s19_r3 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 19 => c.val 0)
        (fun c => (alphaQ_s19_r3 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s19_r3 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s19_r3, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s20_r2 (c : MME.ReleasedInterior.Split 20) : ℚ :=
  (splitWeight 0 20 2 c : ℚ) / 1000000000000

private def jointExponent_s20_r2 (c : MME.ReleasedInterior.Split 20) : ℕ :=
  [6, 3, 7, 9, 2, 2, 9, 7, 3, 6].getD ((seed 0 20).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s20_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 20 => c.val 0)
        (fun c => (splitWeight 0 20 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 20 => (splitWeight 0 20 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 20) : 0 ≤ alphaQ_s20_r2 c := by
    unfold alphaQ_s20_r2
    positivity
  have hprob : ∑ c, alphaQ_s20_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![12738398481,487261481158,487261079120,12739041241,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![13574812103,486425287427,486425711709,13574188761,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s20_r2 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![3,1,3,0,0] ![6,1,1,6,40] ![6,1,1,6,40] jointExponent_s20_r2 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 20 => c.val 0)
        (fun c => (alphaQ_s20_r2 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s20_r2 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s20_r2, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s20_r3 (c : MME.ReleasedInterior.Split 20) : ℚ :=
  (splitWeight 0 20 3 c : ℚ) / 1000000000000

private def jointExponent_s20_r3 (c : MME.ReleasedInterior.Split 20) : ℕ :=
  [7, 3, 7, 9, 2, 2, 9, 7, 3, 7].getD ((seed 0 20).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s20_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 20 => c.val 0)
        (fun c => (splitWeight 0 20 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 20 => (splitWeight 0 20 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 20) : 0 ≤ alphaQ_s20_r3 c := by
    unfold alphaQ_s20_r3
    positivity
  have hprob : ∑ c, alphaQ_s20_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![12290814936,487709083098,487708623513,12291478453,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![12957853402,487042243168,487042705118,12957198312,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s20_r3 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![3,1,3,0,0] ![6,1,1,6,40] ![6,1,1,6,40] jointExponent_s20_r3 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 20 => c.val 0)
        (fun c => (alphaQ_s20_r3 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s20_r3 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s20_r3, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s20_r4 (c : MME.ReleasedInterior.Split 20) : ℚ :=
  (splitWeight 0 20 4 c : ℚ) / 1000000000000

private def jointExponent_s20_r4 (c : MME.ReleasedInterior.Split 20) : ℕ :=
  [7, 3, 6, 9, 2, 2, 9, 6, 3, 7].getD ((seed 0 20).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s20_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 20 => c.val 0)
        (fun c => (splitWeight 0 20 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 20 => (splitWeight 0 20 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 20) : 0 ≤ alphaQ_s20_r4 c := by
    unfold alphaQ_s20_r4
    positivity
  have hprob : ∑ c, alphaQ_s20_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![13653470347,486346501841,486346384147,13653643665,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![12672542392,487327489994,487327617528,12672350086,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s20_r4 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![3,1,3,0,0] ![6,1,1,6,40] ![6,1,1,6,40] jointExponent_s20_r4 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 20 => c.val 0)
        (fun c => (alphaQ_s20_r4 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s20_r4 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s20_r4, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s20_r5 (c : MME.ReleasedInterior.Split 20) : ℚ :=
  (splitWeight 0 20 5 c : ℚ) / 1000000000000

private def jointExponent_s20_r5 (c : MME.ReleasedInterior.Split 20) : ℕ :=
  [7, 3, 7, 9, 2, 2, 9, 7, 3, 7].getD ((seed 0 20).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s20_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 20 => c.val 0)
        (fun c => (splitWeight 0 20 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 20 => (splitWeight 0 20 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 20) : 0 ≤ alphaQ_s20_r5 c := by
    unfold alphaQ_s20_r5
    positivity
  have hprob : ∑ c, alphaQ_s20_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![13043232627,486956734599,486956603606,13043429168,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![12237104528,487762922607,487763080108,12236892757,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s20_r5 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![3,1,3,0,0] ![6,1,1,6,40] ![6,1,1,6,40] jointExponent_s20_r5 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 20 => c.val 0)
        (fun c => (alphaQ_s20_r5 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s20_r5 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s20_r5, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s21_r0 (c : MME.ReleasedInterior.Split 21) : ℚ :=
  (splitWeight 0 21 0 c : ℚ) / 1000000000000

private def jointExponent_s21_r0 (c : MME.ReleasedInterior.Split 21) : ℕ :=
  [3, 5, 12, 5, 1, 5, 12, 5, 3].getD ((seed 0 21).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s21_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 21 => c.val 0)
        (fun c => (splitWeight 0 21 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 21 => (splitWeight 0 21 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 21) : 0 ≤ alphaQ_s21_r0 c := by
    unfold alphaQ_s21_r0
    positivity
  have hprob : ∑ c, alphaQ_s21_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![180472748342,639054585876,180472665782,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![328653757,76183133837,846976462641,76183076053,328673712] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s21_r0 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![3,1,3,0,0] ![3,1,3,40,40] ![12,4,0,4,12] jointExponent_s21_r0 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 21 => c.val 0)
        (fun c => (alphaQ_s21_r0 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s21_r0 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s21_r0, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s21_r1 (c : MME.ReleasedInterior.Split 21) : ℚ :=
  (splitWeight 0 21 1 c : ℚ) / 1000000000000

private def jointExponent_s21_r1 (c : MME.ReleasedInterior.Split 21) : ℕ :=
  [3, 5, 12, 5, 1, 5, 12, 5, 3].getD ((seed 0 21).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s21_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 21 => c.val 0)
        (fun c => (splitWeight 0 21 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 21 => (splitWeight 0 21 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 21) : 0 ≤ alphaQ_s21_r1 c := by
    unfold alphaQ_s21_r1
    positivity
  have hprob : ∑ c, alphaQ_s21_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![183371061413,633257983850,183370954737,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![333571569,77545872780,844241146419,77545775293,333633939] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s21_r1 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![3,1,3,0,0] ![3,1,3,40,40] ![12,4,0,4,12] jointExponent_s21_r1 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 21 => c.val 0)
        (fun c => (alphaQ_s21_r1 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s21_r1 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s21_r1, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s21_r2 (c : MME.ReleasedInterior.Split 21) : ℚ :=
  (splitWeight 0 21 2 c : ℚ) / 1000000000000

private def jointExponent_s21_r2 (c : MME.ReleasedInterior.Split 21) : ℕ :=
  [3, 5, 12, 5, 1, 5, 12, 5, 3].getD ((seed 0 21).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s21_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 21 => c.val 0)
        (fun c => (splitWeight 0 21 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 21 => (splitWeight 0 21 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 21) : 0 ≤ alphaQ_s21_r2 c := by
    unfold alphaQ_s21_r2
    positivity
  have hprob : ∑ c, alphaQ_s21_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![181643610345,636712834401,181643555254,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![328667959,76797622284,845747448905,76797635970,328624882] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s21_r2 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![3,1,3,0,0] ![3,1,3,40,40] ![12,4,0,4,12] jointExponent_s21_r2 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 21 => c.val 0)
        (fun c => (alphaQ_s21_r2 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s21_r2 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s21_r2, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s21_r3 (c : MME.ReleasedInterior.Split 21) : ℚ :=
  (splitWeight 0 21 3 c : ℚ) / 1000000000000

private def jointExponent_s21_r3 (c : MME.ReleasedInterior.Split 21) : ℕ :=
  [3, 5, 12, 5, 1, 5, 12, 5, 3].getD ((seed 0 21).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s21_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 21 => c.val 0)
        (fun c => (splitWeight 0 21 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 21 => (splitWeight 0 21 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 21) : 0 ≤ alphaQ_s21_r3 c := by
    unfold alphaQ_s21_r3
    positivity
  have hprob : ∑ c, alphaQ_s21_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![328714644,76799328748,845743945502,76799343903,328667203] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![181721754281,636556361091,181721884628,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s21_r3 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![3,1,3,0,0] ![12,4,0,4,12] ![3,1,3,40,40] jointExponent_s21_r3 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 21 => c.val 0)
        (fun c => (alphaQ_s21_r3 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s21_r3 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s21_r3, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s21_r4 (c : MME.ReleasedInterior.Split 21) : ℚ :=
  (splitWeight 0 21 4 c : ℚ) / 1000000000000

private def jointExponent_s21_r4 (c : MME.ReleasedInterior.Split 21) : ℕ :=
  [3, 5, 12, 5, 1, 5, 12, 5, 3].getD ((seed 0 21).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s21_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 21 => c.val 0)
        (fun c => (splitWeight 0 21 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 21 => (splitWeight 0 21 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 21) : 0 ≤ alphaQ_s21_r4 c := by
    unfold alphaQ_s21_r4
    positivity
  have hprob : ∑ c, alphaQ_s21_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![333536101,77539983461,844252995224,77539883492,333601722] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![183437600791,633124721643,183437677566,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s21_r4 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![3,1,3,0,0] ![12,4,0,4,12] ![3,1,3,40,40] jointExponent_s21_r4 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 21 => c.val 0)
        (fun c => (alphaQ_s21_r4 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s21_r4 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s21_r4, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s21_r5 (c : MME.ReleasedInterior.Split 21) : ℚ :=
  (splitWeight 0 21 5 c : ℚ) / 1000000000000

private def jointExponent_s21_r5 (c : MME.ReleasedInterior.Split 21) : ℕ :=
  [3, 5, 12, 5, 1, 5, 12, 5, 3].getD ((seed 0 21).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s21_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 21 => c.val 0)
        (fun c => (splitWeight 0 21 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 21 => (splitWeight 0 21 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 21) : 0 ≤ alphaQ_s21_r5 c := by
    unfold alphaQ_s21_r5
    positivity
  have hprob : ∑ c, alphaQ_s21_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![328655025,76184133391,846974462621,76184076156,328672807] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![180542707600,638914480141,180542812259,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s21_r5 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![3,1,3,0,0] ![12,4,0,4,12] ![3,1,3,40,40] jointExponent_s21_r5 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 21 => c.val 0)
        (fun c => (alphaQ_s21_r5 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s21_r5 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s21_r5, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s22_r0 (c : MME.ReleasedInterior.Split 22) : ℚ :=
  (splitWeight 0 22 0 c : ℚ) / 1000000000000

private def jointExponent_s22_r0 (c : MME.ReleasedInterior.Split 22) : ℕ :=
  [3, 7, 2, 2, 7, 3].getD ((seed 0 22).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s22_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 22 => c.val 0)
        (fun c => (splitWeight 0 22 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 22 => (splitWeight 0 22 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 22) : 0 ≤ alphaQ_s22_r0 c := by
    unfold alphaQ_s22_r0
    positivity
  have hprob : ∑ c, alphaQ_s22_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7037857728,492962161807,492961943741,7038036724] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000029984,499999970016,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s22_r0 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![3,1,3,0,0] ![40,7,1,1,7] ![1,1,40,40,40] jointExponent_s22_r0 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 22 => c.val 0)
        (fun c => (alphaQ_s22_r0 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s22_r0 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s22_r0, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s22_r1 (c : MME.ReleasedInterior.Split 22) : ℚ :=
  (splitWeight 0 22 1 c : ℚ) / 1000000000000

private def jointExponent_s22_r1 (c : MME.ReleasedInterior.Split 22) : ℕ :=
  [3, 7, 2, 2, 7, 3].getD ((seed 0 22).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s22_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 22 => c.val 0)
        (fun c => (splitWeight 0 22 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 22 => (splitWeight 0 22 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 22) : 0 ≤ alphaQ_s22_r1 c := by
    unfold alphaQ_s22_r1
    positivity
  have hprob : ∑ c, alphaQ_s22_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7078257432,492921734670,492921734785,7078273113] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000000623,499999999377,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s22_r1 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![3,1,3,0,0] ![40,7,1,1,7] ![1,1,40,40,40] jointExponent_s22_r1 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 22 => c.val 0)
        (fun c => (alphaQ_s22_r1 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s22_r1 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s22_r1, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s22_r3 (c : MME.ReleasedInterior.Split 22) : ℚ :=
  (splitWeight 0 22 3 c : ℚ) / 1000000000000

private def jointExponent_s22_r3 (c : MME.ReleasedInterior.Split 22) : ℕ :=
  [3, 7, 2, 2, 7, 3].getD ((seed 0 22).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s22_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 22 => c.val 0)
        (fun c => (splitWeight 0 22 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 22 => (splitWeight 0 22 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 22) : 0 ≤ alphaQ_s22_r3 c := by
    unfold alphaQ_s22_r3
    positivity
  have hprob : ∑ c, alphaQ_s22_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7151736339,492848094928,492848599585,7151569148] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000278629,499999721371,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s22_r3 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![3,1,3,0,0] ![40,7,1,1,7] ![1,1,40,40,40] jointExponent_s22_r3 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 22 => c.val 0)
        (fun c => (alphaQ_s22_r3 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s22_r3 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s22_r3, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s22_r4 (c : MME.ReleasedInterior.Split 22) : ℚ :=
  (splitWeight 0 22 4 c : ℚ) / 1000000000000

private def jointExponent_s22_r4 (c : MME.ReleasedInterior.Split 22) : ℕ :=
  [3, 7, 2, 2, 7, 3].getD ((seed 0 22).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s22_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 22 => c.val 0)
        (fun c => (splitWeight 0 22 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 22 => (splitWeight 0 22 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 22) : 0 ≤ alphaQ_s22_r4 c := by
    unfold alphaQ_s22_r4
    positivity
  have hprob : ∑ c, alphaQ_s22_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7078587758,492921426781,492921397200,7078588261] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999991715,500000008285,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s22_r4 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![3,1,3,0,0] ![40,7,1,1,7] ![1,1,40,40,40] jointExponent_s22_r4 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 22 => c.val 0)
        (fun c => (alphaQ_s22_r4 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s22_r4 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s22_r4, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s22_r5 (c : MME.ReleasedInterior.Split 22) : ℚ :=
  (splitWeight 0 22 5 c : ℚ) / 1000000000000

private def jointExponent_s22_r5 (c : MME.ReleasedInterior.Split 22) : ℕ :=
  [3, 7, 2, 2, 7, 3].getD ((seed 0 22).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s22_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 22 => c.val 0)
        (fun c => (splitWeight 0 22 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 22 => (splitWeight 0 22 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 22) : 0 ≤ alphaQ_s22_r5 c := by
    unfold alphaQ_s22_r5
    positivity
  have hprob : ∑ c, alphaQ_s22_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7155221199,492844755710,492845177645,7154845446] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999894300,500000105700,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s22_r5 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![3,1,3,0,0] ![40,7,1,1,7] ![1,1,40,40,40] jointExponent_s22_r5 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 22 => c.val 0)
        (fun c => (alphaQ_s22_r5 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s22_r5 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s22_r5, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s25_r0 (c : MME.ReleasedInterior.Split 25) : ℚ :=
  (splitWeight 0 25 0 c : ℚ) / 1000000000000

private def jointExponent_s25_r0 (c : MME.ReleasedInterior.Split 25) : ℕ :=
  [12, 6, 4, 1, 1, 4, 6, 12].getD ((seed 0 25).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s25_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 25 => c.val 0)
        (fun c => (splitWeight 0 25 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 25 => (splitWeight 0 25 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 25) : 0 ≤ alphaQ_s25_r0 c := by
    unfold alphaQ_s25_r0
    positivity
  have hprob : ∑ c, alphaQ_s25_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999974174,500000025826,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![325044509,73635836684,852078232390,73635843381,325043036] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s25_r0 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![6,1,1,6,0] ![1,1,40,40,40] ![12,4,0,4,12] jointExponent_s25_r0 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 25 => c.val 0)
        (fun c => (alphaQ_s25_r0 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s25_r0 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s25_r0, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s25_r1 (c : MME.ReleasedInterior.Split 25) : ℚ :=
  (splitWeight 0 25 1 c : ℚ) / 1000000000000

private def jointExponent_s25_r1 (c : MME.ReleasedInterior.Split 25) : ℕ :=
  [12, 6, 4, 1, 1, 4, 6, 12].getD ((seed 0 25).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s25_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 25 => c.val 0)
        (fun c => (splitWeight 0 25 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 25 => (splitWeight 0 25 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 25) : 0 ≤ alphaQ_s25_r1 c := by
    unfold alphaQ_s25_r1
    positivity
  have hprob : ∑ c, alphaQ_s25_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000000308,499999999692,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![328196851,70621162718,858101285206,70621157851,328197374] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s25_r1 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![6,1,1,6,0] ![1,1,40,40,40] ![12,4,0,4,12] jointExponent_s25_r1 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 25 => c.val 0)
        (fun c => (alphaQ_s25_r1 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s25_r1 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s25_r1, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s25_r2 (c : MME.ReleasedInterior.Split 25) : ℚ :=
  (splitWeight 0 25 2 c : ℚ) / 1000000000000

private def jointExponent_s25_r2 (c : MME.ReleasedInterior.Split 25) : ℕ :=
  [12, 6, 4, 1, 1, 4, 6, 12].getD ((seed 0 25).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s25_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 25 => c.val 0)
        (fun c => (splitWeight 0 25 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 25 => (splitWeight 0 25 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 25) : 0 ≤ alphaQ_s25_r2 c := by
    unfold alphaQ_s25_r2
    positivity
  have hprob : ∑ c, alphaQ_s25_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000025594,499999974406,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![328100100,73617495228,852108821653,73617480499,328102520] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s25_r2 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![6,1,1,6,0] ![1,1,40,40,40] ![12,4,0,4,12] jointExponent_s25_r2 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 25 => c.val 0)
        (fun c => (alphaQ_s25_r2 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s25_r2 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s25_r2, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s26_r0 (c : MME.ReleasedInterior.Split 26) : ℚ :=
  (splitWeight 0 26 0 c : ℚ) / 1000000000000

private def jointExponent_s26_r0 (c : MME.ReleasedInterior.Split 26) : ℕ :=
  [9, 7, 6, 2, 3, 3, 2, 6, 7, 9].getD ((seed 0 26).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s26_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 26 => c.val 0)
        (fun c => (splitWeight 0 26 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 26 => (splitWeight 0 26 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 26) : 0 ≤ alphaQ_s26_r0 c := by
    unfold alphaQ_s26_r0
    positivity
  have hprob : ∑ c, alphaQ_s26_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![12850492378,487149506349,487149531377,12850469896,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![13575897434,486424097301,486424104246,13575901019,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s26_r0 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![6,1,1,6,0] ![6,1,1,6,40] ![6,1,1,6,40] jointExponent_s26_r0 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 26 => c.val 0)
        (fun c => (alphaQ_s26_r0 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s26_r0 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s26_r0, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s26_r1 (c : MME.ReleasedInterior.Split 26) : ℚ :=
  (splitWeight 0 26 1 c : ℚ) / 1000000000000

private def jointExponent_s26_r1 (c : MME.ReleasedInterior.Split 26) : ℕ :=
  [9, 7, 7, 2, 3, 3, 2, 7, 7, 9].getD ((seed 0 26).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s26_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 26 => c.val 0)
        (fun c => (splitWeight 0 26 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 26 => (splitWeight 0 26 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 26) : 0 ≤ alphaQ_s26_r1 c := by
    unfold alphaQ_s26_r1
    positivity
  have hprob : ∑ c, alphaQ_s26_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![12398575535,487601427168,487601456819,12398540478,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![12957336124,487042656968,487042644212,12957362696,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s26_r1 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![6,1,1,6,0] ![6,1,1,6,40] ![6,1,1,6,40] jointExponent_s26_r1 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 26 => c.val 0)
        (fun c => (alphaQ_s26_r1 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s26_r1 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s26_r1, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s26_r4 (c : MME.ReleasedInterior.Split 26) : ℚ :=
  (splitWeight 0 26 4 c : ℚ) / 1000000000000

private def jointExponent_s26_r4 (c : MME.ReleasedInterior.Split 26) : ℕ :=
  [9, 7, 7, 2, 3, 3, 2, 7, 7, 9].getD ((seed 0 26).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s26_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 26 => c.val 0)
        (fun c => (splitWeight 0 26 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 26 => (splitWeight 0 26 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 26) : 0 ≤ alphaQ_s26_r4 c := by
    unfold alphaQ_s26_r4
    positivity
  have hprob : ∑ c, alphaQ_s26_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![13163574224,486836423683,486836434798,13163567295,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![12253843137,487746155540,487746158215,12253843108,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s26_r4 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![6,1,1,6,0] ![6,1,1,6,40] ![6,1,1,6,40] jointExponent_s26_r4 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 26 => c.val 0)
        (fun c => (alphaQ_s26_r4 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s26_r4 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s26_r4, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s26_r5 (c : MME.ReleasedInterior.Split 26) : ℚ :=
  (splitWeight 0 26 5 c : ℚ) / 1000000000000

private def jointExponent_s26_r5 (c : MME.ReleasedInterior.Split 26) : ℕ :=
  [9, 6, 7, 2, 3, 3, 2, 7, 6, 9].getD ((seed 0 26).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s26_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 26 => c.val 0)
        (fun c => (splitWeight 0 26 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 26 => (splitWeight 0 26 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 26) : 0 ≤ alphaQ_s26_r5 c := by
    unfold alphaQ_s26_r5
    positivity
  have hprob : ∑ c, alphaQ_s26_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![13769678930,486230320636,486230337018,13769663416,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![12682325093,487317672055,487317670297,12682332555,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s26_r5 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![6,1,1,6,0] ![6,1,1,6,40] ![6,1,1,6,40] jointExponent_s26_r5 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 26 => c.val 0)
        (fun c => (alphaQ_s26_r5 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s26_r5 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s26_r5, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s27_r0 (c : MME.ReleasedInterior.Split 27) : ℚ :=
  (splitWeight 0 27 0 c : ℚ) / 1000000000000

private def jointExponent_s27_r0 (c : MME.ReleasedInterior.Split 27) : ℕ :=
  [7, 9, 3, 2, 7, 7, 2, 3, 9, 7].getD ((seed 0 27).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s27_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 27 => c.val 0)
        (fun c => (splitWeight 0 27 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 27 => (splitWeight 0 27 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 27) : 0 ≤ alphaQ_s27_r0 c := by
    unfold alphaQ_s27_r0
    positivity
  have hprob : ∑ c, alphaQ_s27_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![12406625144,487593437082,487593388465,12406549309,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![13043424600,486956616038,486956463724,13043495638,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s27_r0 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![6,1,1,6,0] ![6,1,1,6,40] ![6,1,1,6,40] jointExponent_s27_r0 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 27 => c.val 0)
        (fun c => (alphaQ_s27_r0 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s27_r0 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s27_r0, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s27_r1 (c : MME.ReleasedInterior.Split 27) : ℚ :=
  (splitWeight 0 27 1 c : ℚ) / 1000000000000

private def jointExponent_s27_r1 (c : MME.ReleasedInterior.Split 27) : ℕ :=
  [7, 9, 3, 2, 6, 6, 2, 3, 9, 7].getD ((seed 0 27).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s27_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 27 => c.val 0)
        (fun c => (splitWeight 0 27 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 27 => (splitWeight 0 27 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 27) : 0 ≤ alphaQ_s27_r1 c := by
    unfold alphaQ_s27_r1
    positivity
  have hprob : ∑ c, alphaQ_s27_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![12853781789,487146284216,487146251242,12853682753,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![13661764579,486338271572,486338110249,13661853600,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s27_r1 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![6,1,1,6,0] ![6,1,1,6,40] ![6,1,1,6,40] jointExponent_s27_r1 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 27 => c.val 0)
        (fun c => (alphaQ_s27_r1 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s27_r1 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s27_r1, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s27_r2 (c : MME.ReleasedInterior.Split 27) : ℚ :=
  (splitWeight 0 27 2 c : ℚ) / 1000000000000

private def jointExponent_s27_r2 (c : MME.ReleasedInterior.Split 27) : ℕ :=
  [7, 9, 3, 2, 7, 7, 2, 3, 9, 7].getD ((seed 0 27).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s27_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 27 => c.val 0)
        (fun c => (splitWeight 0 27 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 27 => (splitWeight 0 27 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 27) : 0 ≤ alphaQ_s27_r2 c := by
    unfold alphaQ_s27_r2
    positivity
  have hprob : ∑ c, alphaQ_s27_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![13162714611,486837338901,486837236292,13162710196,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![12316208226,487683840855,487683741057,12316209862,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s27_r2 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![6,1,1,6,0] ![6,1,1,6,40] ![6,1,1,6,40] jointExponent_s27_r2 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 27 => c.val 0)
        (fun c => (alphaQ_s27_r2 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s27_r2 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s27_r2, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s27_r3 (c : MME.ReleasedInterior.Split 27) : ℚ :=
  (splitWeight 0 27 3 c : ℚ) / 1000000000000

private def jointExponent_s27_r3 (c : MME.ReleasedInterior.Split 27) : ℕ :=
  [6, 9, 3, 2, 7, 7, 2, 3, 9, 6].getD ((seed 0 27).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s27_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 27 => c.val 0)
        (fun c => (splitWeight 0 27 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 27 => (splitWeight 0 27 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 27) : 0 ≤ alphaQ_s27_r3 c := by
    unfold alphaQ_s27_r3
    positivity
  have hprob : ∑ c, alphaQ_s27_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![13775708861,486224343744,486224241985,13775705410,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![12750263426,487249785940,487249688880,12750261754,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s27_r3 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![6,1,1,6,0] ![6,1,1,6,40] ![6,1,1,6,40] jointExponent_s27_r3 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 27 => c.val 0)
        (fun c => (alphaQ_s27_r3 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s27_r3 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s27_r3, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s28_r0 (c : MME.ReleasedInterior.Split 28) : ℚ :=
  (splitWeight 0 28 0 c : ℚ) / 1000000000000

private def jointExponent_s28_r0 (c : MME.ReleasedInterior.Split 28) : ℕ :=
  [6, 12, 1, 4, 4, 1, 12, 6].getD ((seed 0 28).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s28_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 28 => c.val 0)
        (fun c => (splitWeight 0 28 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 28 => (splitWeight 0 28 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 28) : 0 ≤ alphaQ_s28_r0 c := by
    unfold alphaQ_s28_r0
    positivity
  have hprob : ∑ c, alphaQ_s28_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![328217830,74882013843,849579539576,74882000439,328228312] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000009813,499999990187,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s28_r0 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![6,1,1,6,0] ![12,4,0,4,12] ![1,1,40,40,40] jointExponent_s28_r0 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 28 => c.val 0)
        (fun c => (alphaQ_s28_r0 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s28_r0 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s28_r0, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s28_r1 (c : MME.ReleasedInterior.Split 28) : ℚ :=
  (splitWeight 0 28 1 c : ℚ) / 1000000000000

private def jointExponent_s28_r1 (c : MME.ReleasedInterior.Split 28) : ℕ :=
  [6, 12, 1, 4, 4, 1, 12, 6].getD ((seed 0 28).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s28_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 28 => c.val 0)
        (fun c => (splitWeight 0 28 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 28 => (splitWeight 0 28 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 28) : 0 ≤ alphaQ_s28_r1 c := by
    unfold alphaQ_s28_r1
    positivity
  have hprob : ∑ c, alphaQ_s28_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![328490354,77725297974,843892421542,77725293824,328496306] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999995331,500000004669,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s28_r1 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![6,1,1,6,0] ![12,4,0,4,12] ![1,1,40,40,40] jointExponent_s28_r1 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 28 => c.val 0)
        (fun c => (alphaQ_s28_r1 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s28_r1 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s28_r1, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s28_r4 (c : MME.ReleasedInterior.Split 28) : ℚ :=
  (splitWeight 0 28 4 c : ℚ) / 1000000000000

private def jointExponent_s28_r4 (c : MME.ReleasedInterior.Split 28) : ℕ :=
  [6, 12, 1, 4, 4, 1, 12, 6].getD ((seed 0 28).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s28_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 28 => c.val 0)
        (fun c => (splitWeight 0 28 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 28 => (splitWeight 0 28 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 28) : 0 ≤ alphaQ_s28_r4 c := by
    unfold alphaQ_s28_r4
    positivity
  have hprob : ∑ c, alphaQ_s28_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![330483859,77756736826,843825562957,77756735605,330480753] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000002138,499999997862,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s28_r4 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![6,1,1,6,0] ![12,4,0,4,12] ![1,1,40,40,40] jointExponent_s28_r4 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 28 => c.val 0)
        (fun c => (alphaQ_s28_r4 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s28_r4 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s28_r4, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s31_r3 (c : MME.ReleasedInterior.Split 31) : ℚ :=
  (splitWeight 0 31 3 c : ℚ) / 1000000000000

private def jointExponent_s31_r3 (c : MME.ReleasedInterior.Split 31) : ℕ :=
  [12, 6, 4, 1, 1, 4, 6, 12].getD ((seed 0 31).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s31_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 31 => c.val 0)
        (fun c => (splitWeight 0 31 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 31 => (splitWeight 0 31 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 31) : 0 ≤ alphaQ_s31_r3 c := by
    unfold alphaQ_s31_r3
    positivity
  have hprob : ∑ c, alphaQ_s31_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![328745515,80539057868,838264385569,80539065474,328745574] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999984676,500000015324,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s31_r3 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![12,4,0,4,12] ![12,4,0,4,12] ![1,1,40,40,40] jointExponent_s31_r3 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 31 => c.val 0)
        (fun c => (alphaQ_s31_r3 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s31_r3 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s31_r3, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s31_r4 (c : MME.ReleasedInterior.Split 31) : ℚ :=
  (splitWeight 0 31 4 c : ℚ) / 1000000000000

private def jointExponent_s31_r4 (c : MME.ReleasedInterior.Split 31) : ℕ :=
  [12, 6, 4, 1, 1, 4, 6, 12].getD ((seed 0 31).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s31_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 31 => c.val 0)
        (fun c => (splitWeight 0 31 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 31 => (splitWeight 0 31 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 31) : 0 ≤ alphaQ_s31_r4 c := by
    unfold alphaQ_s31_r4
    positivity
  have hprob : ∑ c, alphaQ_s31_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![324702446,77738799055,843872990805,77738803788,324703906] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999989960,500000010040,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s31_r4 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![12,4,0,4,12] ![12,4,0,4,12] ![1,1,40,40,40] jointExponent_s31_r4 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 31 => c.val 0)
        (fun c => (alphaQ_s31_r4 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s31_r4 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s31_r4, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s31_r5 (c : MME.ReleasedInterior.Split 31) : ℚ :=
  (splitWeight 0 31 5 c : ℚ) / 1000000000000

private def jointExponent_s31_r5 (c : MME.ReleasedInterior.Split 31) : ℕ :=
  [12, 6, 4, 1, 1, 4, 6, 12].getD ((seed 0 31).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s31_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 31 => c.val 0)
        (fun c => (splitWeight 0 31 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 31 => (splitWeight 0 31 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 31) : 0 ≤ alphaQ_s31_r5 c := by
    unfold alphaQ_s31_r5
    positivity
  have hprob : ∑ c, alphaQ_s31_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![327524255,80460781617,838423366845,80460804192,327523091] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999956907,500000043093,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s31_r5 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![12,4,0,4,12] ![12,4,0,4,12] ![1,1,40,40,40] jointExponent_s31_r5 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 31 => c.val 0)
        (fun c => (alphaQ_s31_r5 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s31_r5 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s31_r5, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s32_r0 (c : MME.ReleasedInterior.Split 32) : ℚ :=
  (splitWeight 0 32 0 c : ℚ) / 1000000000000

private def jointExponent_s32_r0 (c : MME.ReleasedInterior.Split 32) : ℕ :=
  [12, 5, 5, 3, 1, 3, 5, 5, 12].getD ((seed 0 32).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s32_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 32 => c.val 0)
        (fun c => (splitWeight 0 32 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 32 => (splitWeight 0 32 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 32) : 0 ≤ alphaQ_s32_r0 c := by
    unfold alphaQ_s32_r0
    positivity
  have hprob : ∑ c, alphaQ_s32_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![336214340,79861582527,839604442775,79861623042,336137316] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![181833572564,636332889637,181833537799,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s32_r0 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![12,4,0,4,12] ![12,4,0,4,12] ![3,1,3,40,40] jointExponent_s32_r0 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 32 => c.val 0)
        (fun c => (alphaQ_s32_r0 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s32_r0 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s32_r0, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s32_r1 (c : MME.ReleasedInterior.Split 32) : ℚ :=
  (splitWeight 0 32 1 c : ℚ) / 1000000000000

private def jointExponent_s32_r1 (c : MME.ReleasedInterior.Split 32) : ℕ :=
  [12, 5, 5, 3, 1, 3, 5, 5, 12].getD ((seed 0 32).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s32_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 32 => c.val 0)
        (fun c => (splitWeight 0 32 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 32 => (splitWeight 0 32 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 32) : 0 ≤ alphaQ_s32_r1 c := by
    unfold alphaQ_s32_r1
    positivity
  have hprob : ∑ c, alphaQ_s32_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![336167787,79860818860,839606064309,79860837774,336111270] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![181880129254,636239603131,181880267615,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s32_r1 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![12,4,0,4,12] ![12,4,0,4,12] ![3,1,3,40,40] jointExponent_s32_r1 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 32 => c.val 0)
        (fun c => (alphaQ_s32_r1 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s32_r1 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s32_r1, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s32_r2 (c : MME.ReleasedInterior.Split 32) : ℚ :=
  (splitWeight 0 32 2 c : ℚ) / 1000000000000

private def jointExponent_s32_r2 (c : MME.ReleasedInterior.Split 32) : ℕ :=
  [12, 5, 5, 3, 1, 3, 5, 5, 12].getD ((seed 0 32).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s32_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 32 => c.val 0)
        (fun c => (splitWeight 0 32 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 32 => (splitWeight 0 32 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 32) : 0 ≤ alphaQ_s32_r2 c := by
    unfold alphaQ_s32_r2
    positivity
  have hprob : ∑ c, alphaQ_s32_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![335730793,79186652541,840955268571,79186623307,335724788] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![180582040222,638835990232,180581969546,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s32_r2 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![12,4,0,4,12] ![12,4,0,4,12] ![3,1,3,40,40] jointExponent_s32_r2 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 32 => c.val 0)
        (fun c => (alphaQ_s32_r2 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s32_r2 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s32_r2, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s32_r4 (c : MME.ReleasedInterior.Split 32) : ℚ :=
  (splitWeight 0 32 4 c : ℚ) / 1000000000000

private def jointExponent_s32_r4 (c : MME.ReleasedInterior.Split 32) : ℕ :=
  [12, 5, 5, 3, 1, 3, 5, 5, 12].getD ((seed 0 32).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s32_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 32 => c.val 0)
        (fun c => (splitWeight 0 32 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 32 => (splitWeight 0 32 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 32) : 0 ≤ alphaQ_s32_r4 c := by
    unfold alphaQ_s32_r4
    positivity
  have hprob : ∑ c, alphaQ_s32_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![335766578,79189241061,840950020940,79189188882,335782539] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![180622026527,638755840543,180622132930,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s32_r4 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![12,4,0,4,12] ![12,4,0,4,12] ![3,1,3,40,40] jointExponent_s32_r4 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 32 => c.val 0)
        (fun c => (alphaQ_s32_r4 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s32_r4 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s32_r4, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s33_r2 (c : MME.ReleasedInterior.Split 33) : ℚ :=
  (splitWeight 0 33 2 c : ℚ) / 1000000000000

private def jointExponent_s33_r2 (c : MME.ReleasedInterior.Split 33) : ℕ :=
  [12, 4, 6, 1, 1, 6, 4, 12].getD ((seed 0 33).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s33_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 33 => c.val 0)
        (fun c => (splitWeight 0 33 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 33 => (splitWeight 0 33 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 33) : 0 ≤ alphaQ_s33_r2 c := by
    unfold alphaQ_s33_r2
    positivity
  have hprob : ∑ c, alphaQ_s33_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![326416815,77745783785,843855602961,77745778170,326418269] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000010690,499999989310,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s33_r2 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![12,4,0,4,12] ![12,4,0,4,12] ![1,1,40,40,40] jointExponent_s33_r2 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 33 => c.val 0)
        (fun c => (alphaQ_s33_r2 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s33_r2 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s33_r2, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s33_r3 (c : MME.ReleasedInterior.Split 33) : ℚ :=
  (splitWeight 0 33 3 c : ℚ) / 1000000000000

private def jointExponent_s33_r3 (c : MME.ReleasedInterior.Split 33) : ℕ :=
  [12, 4, 6, 1, 1, 6, 4, 12].getD ((seed 0 33).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s33_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 33 => c.val 0)
        (fun c => (splitWeight 0 33 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 33 => (splitWeight 0 33 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 33) : 0 ≤ alphaQ_s33_r3 c := by
    unfold alphaQ_s33_r3
    positivity
  have hprob : ∑ c, alphaQ_s33_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![328728191,80484738082,838373071604,80484734039,328728084] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000004437,499999995563,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s33_r3 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![12,4,0,4,12] ![12,4,0,4,12] ![1,1,40,40,40] jointExponent_s33_r3 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 33 => c.val 0)
        (fun c => (alphaQ_s33_r3 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s33_r3 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s33_r3, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s33_r5 (c : MME.ReleasedInterior.Split 33) : ℚ :=
  (splitWeight 0 33 5 c : ℚ) / 1000000000000

private def jointExponent_s33_r5 (c : MME.ReleasedInterior.Split 33) : ℕ :=
  [12, 4, 6, 1, 1, 6, 4, 12].getD ((seed 0 33).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s33_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 33 => c.val 0)
        (fun c => (splitWeight 0 33 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 33 => (splitWeight 0 33 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 33) : 0 ≤ alphaQ_s33_r5 c := by
    unfold alphaQ_s33_r5
    positivity
  have hprob : ∑ c, alphaQ_s33_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![330075203,80554173746,838231507420,80554168138,330075493] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000011017,499999988983,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s33_r5 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![12,4,0,4,12] ![12,4,0,4,12] ![1,1,40,40,40] jointExponent_s33_r5 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 33 => c.val 0)
        (fun c => (alphaQ_s33_r5 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s33_r5 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s33_r5, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s36_r0 (c : MME.ReleasedInterior.Split 36) : ℚ :=
  (splitWeight 0 36 0 c : ℚ) / 1000000000000

private def jointExponent_s36_r0 (c : MME.ReleasedInterior.Split 36) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 0 36).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s36_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 36 => c.val 0)
        (fun c => (splitWeight 0 36 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 36 => (splitWeight 0 36 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 36) : 0 ≤ alphaQ_s36_r0 c := by
    unfold alphaQ_s36_r0
    positivity
  have hprob : ∑ c, alphaQ_s36_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7315321847,492684726034,492684634167,7315317952] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000053715,499999946285,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s36_r0 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![0,7,1,1,7] ![40,7,1,1,7] ![1,1,40,40,40] jointExponent_s36_r0 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 36 => c.val 0)
        (fun c => (alphaQ_s36_r0 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s36_r0 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s36_r0, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s36_r2 (c : MME.ReleasedInterior.Split 36) : ℚ :=
  (splitWeight 0 36 2 c : ℚ) / 1000000000000

private def jointExponent_s36_r2 (c : MME.ReleasedInterior.Split 36) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 0 36).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s36_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 36 => c.val 0)
        (fun c => (splitWeight 0 36 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 36 => (splitWeight 0 36 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 36) : 0 ≤ alphaQ_s36_r2 c := by
    unfold alphaQ_s36_r2
    positivity
  have hprob : ∑ c, alphaQ_s36_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7327900395,492672167378,492672053366,7327878861] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000031143,499999968857,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s36_r2 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![0,7,1,1,7] ![40,7,1,1,7] ![1,1,40,40,40] jointExponent_s36_r2 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 36 => c.val 0)
        (fun c => (alphaQ_s36_r2 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s36_r2 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s36_r2, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s36_r3 (c : MME.ReleasedInterior.Split 36) : ℚ :=
  (splitWeight 0 36 3 c : ℚ) / 1000000000000

private def jointExponent_s36_r3 (c : MME.ReleasedInterior.Split 36) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 0 36).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s36_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 36 => c.val 0)
        (fun c => (splitWeight 0 36 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 36 => (splitWeight 0 36 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 36) : 0 ≤ alphaQ_s36_r3 c := by
    unfold alphaQ_s36_r3
    positivity
  have hprob : ∑ c, alphaQ_s36_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7367684162,492632366694,492632274789,7367674355] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000049991,499999950009,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s36_r3 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![0,7,1,1,7] ![40,7,1,1,7] ![1,1,40,40,40] jointExponent_s36_r3 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 36 => c.val 0)
        (fun c => (alphaQ_s36_r3 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s36_r3 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s36_r3, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s36_r4 (c : MME.ReleasedInterior.Split 36) : ℚ :=
  (splitWeight 0 36 4 c : ℚ) / 1000000000000

private def jointExponent_s36_r4 (c : MME.ReleasedInterior.Split 36) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 0 36).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s36_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 36 => c.val 0)
        (fun c => (splitWeight 0 36 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 36 => (splitWeight 0 36 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 36) : 0 ≤ alphaQ_s36_r4 c := by
    unfold alphaQ_s36_r4
    positivity
  have hprob : ∑ c, alphaQ_s36_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7255845994,492744203651,492744093402,7255856953] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000058824,499999941176,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s36_r4 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![0,7,1,1,7] ![40,7,1,1,7] ![1,1,40,40,40] jointExponent_s36_r4 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 36 => c.val 0)
        (fun c => (alphaQ_s36_r4 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s36_r4 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s36_r4, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s36_r5 (c : MME.ReleasedInterior.Split 36) : ℚ :=
  (splitWeight 0 36 5 c : ℚ) / 1000000000000

private def jointExponent_s36_r5 (c : MME.ReleasedInterior.Split 36) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 0 36).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s36_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 36 => c.val 0)
        (fun c => (splitWeight 0 36 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 36 => (splitWeight 0 36 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 36) : 0 ≤ alphaQ_s36_r5 c := by
    unfold alphaQ_s36_r5
    positivity
  have hprob : ∑ c, alphaQ_s36_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7353501646,492646550959,492646440721,7353506674] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000055231,499999944769,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s36_r5 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![0,7,1,1,7] ![40,7,1,1,7] ![1,1,40,40,40] jointExponent_s36_r5 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 36 => c.val 0)
        (fun c => (alphaQ_s36_r5 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s36_r5 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s36_r5, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s37_r1 (c : MME.ReleasedInterior.Split 37) : ℚ :=
  (splitWeight 0 37 1 c : ℚ) / 1000000000000

private def jointExponent_s37_r1 (c : MME.ReleasedInterior.Split 37) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 0 37).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s37_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 37 => c.val 0)
        (fun c => (splitWeight 0 37 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 37 => (splitWeight 0 37 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 37) : 0 ≤ alphaQ_s37_r1 c := by
    unfold alphaQ_s37_r1
    positivity
  have hprob : ∑ c, alphaQ_s37_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7314898303,492685087925,492685115133,7314898639] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000005689,499999994311,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s37_r1 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![0,7,1,1,7] ![40,7,1,1,7] ![1,1,40,40,40] jointExponent_s37_r1 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 37 => c.val 0)
        (fun c => (alphaQ_s37_r1 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s37_r1 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s37_r1, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s37_r2 (c : MME.ReleasedInterior.Split 37) : ℚ :=
  (splitWeight 0 37 2 c : ℚ) / 1000000000000

private def jointExponent_s37_r2 (c : MME.ReleasedInterior.Split 37) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 0 37).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s37_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 37 => c.val 0)
        (fun c => (splitWeight 0 37 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 37 => (splitWeight 0 37 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 37) : 0 ≤ alphaQ_s37_r2 c := by
    unfold alphaQ_s37_r2
    positivity
  have hprob : ∑ c, alphaQ_s37_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7255512713,492744493668,492744490575,7255503044] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999992033,500000007967,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s37_r2 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![0,7,1,1,7] ![40,7,1,1,7] ![1,1,40,40,40] jointExponent_s37_r2 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 37 => c.val 0)
        (fun c => (alphaQ_s37_r2 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s37_r2 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s37_r2, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s37_r3 (c : MME.ReleasedInterior.Split 37) : ℚ :=
  (splitWeight 0 37 3 c : ℚ) / 1000000000000

private def jointExponent_s37_r3 (c : MME.ReleasedInterior.Split 37) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 0 37).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s37_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 37 => c.val 0)
        (fun c => (splitWeight 0 37 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 37 => (splitWeight 0 37 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 37) : 0 ≤ alphaQ_s37_r3 c := by
    unfold alphaQ_s37_r3
    positivity
  have hprob : ∑ c, alphaQ_s37_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7353690373,492646097773,492648795661,7351416193] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999368173,500000631827,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s37_r3 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![0,7,1,1,7] ![40,7,1,1,7] ![1,1,40,40,40] jointExponent_s37_r3 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 37 => c.val 0)
        (fun c => (alphaQ_s37_r3 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s37_r3 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s37_r3, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s37_r4 (c : MME.ReleasedInterior.Split 37) : ℚ :=
  (splitWeight 0 37 4 c : ℚ) / 1000000000000

private def jointExponent_s37_r4 (c : MME.ReleasedInterior.Split 37) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 0 37).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s37_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 37 => c.val 0)
        (fun c => (splitWeight 0 37 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 37 => (splitWeight 0 37 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 37) : 0 ≤ alphaQ_s37_r4 c := by
    unfold alphaQ_s37_r4
    positivity
  have hprob : ∑ c, alphaQ_s37_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7326923751,492673050596,492673103056,7326922597] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000022701,499999977299,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s37_r4 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![0,7,1,1,7] ![40,7,1,1,7] ![1,1,40,40,40] jointExponent_s37_r4 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 37 => c.val 0)
        (fun c => (alphaQ_s37_r4 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s37_r4 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s37_r4, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s37_r5 (c : MME.ReleasedInterior.Split 37) : ℚ :=
  (splitWeight 0 37 5 c : ℚ) / 1000000000000

private def jointExponent_s37_r5 (c : MME.ReleasedInterior.Split 37) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 0 37).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s37_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 37 => c.val 0)
        (fun c => (splitWeight 0 37 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 37 => (splitWeight 0 37 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 37) : 0 ≤ alphaQ_s37_r5 c := by
    unfold alphaQ_s37_r5
    positivity
  have hprob : ∑ c, alphaQ_s37_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7368331106,492631665502,492631688563,7368314829] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999997315,500000002685,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s37_r5 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![0,7,1,1,7] ![40,7,1,1,7] ![1,1,40,40,40] jointExponent_s37_r5 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 37 => c.val 0)
        (fun c => (alphaQ_s37_r5 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s37_r5 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s37_r5, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s40_r0 (c : MME.ReleasedInterior.Split 40) : ℚ :=
  (splitWeight 0 40 0 c : ℚ) / 1000000000000

private def jointExponent_s40_r0 (c : MME.ReleasedInterior.Split 40) : ℕ :=
  [3, 1, 1, 3].getD ((seed 0 40).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s40_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 40 => c.val 0)
        (fun c => (splitWeight 0 40 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 40 => (splitWeight 0 40 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 40) : 0 ≤ alphaQ_s40_r0 c := by
    unfold alphaQ_s40_r0
    positivity
  have hprob : ∑ c, alphaQ_s40_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999995198,500000004802,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999995204,500000004796,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s40_r0 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![0,0,3,0,3] ![1,1,40,40,40] ![1,1,40,40,40] jointExponent_s40_r0 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 40 => c.val 0)
        (fun c => (alphaQ_s40_r0 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s40_r0 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s40_r0, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s40_r1 (c : MME.ReleasedInterior.Split 40) : ℚ :=
  (splitWeight 0 40 1 c : ℚ) / 1000000000000

private def jointExponent_s40_r1 (c : MME.ReleasedInterior.Split 40) : ℕ :=
  [3, 1, 1, 3].getD ((seed 0 40).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s40_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 40 => c.val 0)
        (fun c => (splitWeight 0 40 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 40 => (splitWeight 0 40 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 40) : 0 ≤ alphaQ_s40_r1 c := by
    unfold alphaQ_s40_r1
    positivity
  have hprob : ∑ c, alphaQ_s40_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999998856,500000001144,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999997261,500000002739,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s40_r1 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![0,0,3,0,3] ![1,1,40,40,40] ![1,1,40,40,40] jointExponent_s40_r1 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 40 => c.val 0)
        (fun c => (alphaQ_s40_r1 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s40_r1 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s40_r1, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s40_r2 (c : MME.ReleasedInterior.Split 40) : ℚ :=
  (splitWeight 0 40 2 c : ℚ) / 1000000000000

private def jointExponent_s40_r2 (c : MME.ReleasedInterior.Split 40) : ℕ :=
  [3, 1, 1, 3].getD ((seed 0 40).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s40_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 40 => c.val 0)
        (fun c => (splitWeight 0 40 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 40 => (splitWeight 0 40 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 40) : 0 ≤ alphaQ_s40_r2 c := by
    unfold alphaQ_s40_r2
    positivity
  have hprob : ∑ c, alphaQ_s40_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999998651,500000001349,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999997899,500000002101,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s40_r2 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![0,0,3,0,3] ![1,1,40,40,40] ![1,1,40,40,40] jointExponent_s40_r2 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 40 => c.val 0)
        (fun c => (alphaQ_s40_r2 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s40_r2 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s40_r2, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s40_r3 (c : MME.ReleasedInterior.Split 40) : ℚ :=
  (splitWeight 0 40 3 c : ℚ) / 1000000000000

private def jointExponent_s40_r3 (c : MME.ReleasedInterior.Split 40) : ℕ :=
  [3, 1, 1, 3].getD ((seed 0 40).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s40_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 40 => c.val 0)
        (fun c => (splitWeight 0 40 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 40 => (splitWeight 0 40 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 40) : 0 ≤ alphaQ_s40_r3 c := by
    unfold alphaQ_s40_r3
    positivity
  have hprob : ∑ c, alphaQ_s40_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999999936,500000000064,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999999938,500000000062,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s40_r3 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![0,0,3,0,3] ![1,1,40,40,40] ![1,1,40,40,40] jointExponent_s40_r3 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 40 => c.val 0)
        (fun c => (alphaQ_s40_r3 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s40_r3 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s40_r3, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s40_r4 (c : MME.ReleasedInterior.Split 40) : ℚ :=
  (splitWeight 0 40 4 c : ℚ) / 1000000000000

private def jointExponent_s40_r4 (c : MME.ReleasedInterior.Split 40) : ℕ :=
  [3, 1, 1, 3].getD ((seed 0 40).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s40_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 40 => c.val 0)
        (fun c => (splitWeight 0 40 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 40 => (splitWeight 0 40 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 40) : 0 ≤ alphaQ_s40_r4 c := by
    unfold alphaQ_s40_r4
    positivity
  have hprob : ∑ c, alphaQ_s40_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999997762,500000002238,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999998279,500000001721,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s40_r4 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![0,0,3,0,3] ![1,1,40,40,40] ![1,1,40,40,40] jointExponent_s40_r4 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 40 => c.val 0)
        (fun c => (alphaQ_s40_r4 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s40_r4 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s40_r4, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s40_r5 (c : MME.ReleasedInterior.Split 40) : ℚ :=
  (splitWeight 0 40 5 c : ℚ) / 1000000000000

private def jointExponent_s40_r5 (c : MME.ReleasedInterior.Split 40) : ℕ :=
  [3, 1, 1, 3].getD ((seed 0 40).splits.idxOf (sourceShape 0 c)) 0

private theorem region_s40_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 40 => c.val 0)
        (fun c => (splitWeight 0 40 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 40 => (splitWeight 0 40 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 40) : 0 ≤ alphaQ_s40_r5 c := by
    unfold alphaQ_s40_r5
    positivity
  have hprob : ∑ c, alphaQ_s40_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999997337,500000002663,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999997800,500000002200,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s40_r5 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![0,0,3,0,3] ![1,1,40,40,40] ![1,1,40,40,40] jointExponent_s40_r5 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 40 => c.val 0)
        (fun c => (alphaQ_s40_r5 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s40_r5 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s40_r5, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

/-- Every nonempty region of this owner's released interior recipes has
coarse entropy minus the maximum-entropy penalty at least two fifths. -/
theorem solution
    (s : Fin 45) (r : Fin 6) (hi : (seed 0 s).boundary = [])
    (hn : 0 < (seed 0 s).region.getD r.val 0) :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split s => c.val 0)
        (fun c => (splitWeight 0 s r c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split s => (splitWeight 0 s r c : ℝ) / 1000000000000) := by
  fin_cases s
  · exact False.elim ((by decide +kernel : (seed 0 0).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 0 1).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 0 2).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 0 3).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 0 4).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 0 5).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 0 6).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 0 7).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 0 8).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 0 9).boundary ≠ []) hi)
  · fin_cases r
    · exact region_s10_r0
    · exact region_s10_r1
    · exact region_s10_r2
    · exact region_s10_r3
    · exact region_s10_r4
    · exact region_s10_r5
  · fin_cases r
    · exact region_s11_r0
    · have hz : (seed 0 11).region.getD 1 0 = 0 := by decide +kernel
      change 0 < (seed 0 11).region.getD 1 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s11_r2
    · exact region_s11_r3
    · have hz : (seed 0 11).region.getD 4 0 = 0 := by decide +kernel
      change 0 < (seed 0 11).region.getD 4 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 0 11).region.getD 5 0 = 0 := by decide +kernel
      change 0 < (seed 0 11).region.getD 5 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
  · fin_cases r
    · exact region_s12_r0
    · have hz : (seed 0 12).region.getD 1 0 = 0 := by decide +kernel
      change 0 < (seed 0 12).region.getD 1 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s12_r2
    · exact region_s12_r3
    · have hz : (seed 0 12).region.getD 4 0 = 0 := by decide +kernel
      change 0 < (seed 0 12).region.getD 4 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 0 12).region.getD 5 0 = 0 := by decide +kernel
      change 0 < (seed 0 12).region.getD 5 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
  · fin_cases r
    · have hz : (seed 0 13).region.getD 0 0 = 0 := by decide +kernel
      change 0 < (seed 0 13).region.getD 0 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s13_r1
    · have hz : (seed 0 13).region.getD 2 0 = 0 := by decide +kernel
      change 0 < (seed 0 13).region.getD 2 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 0 13).region.getD 3 0 = 0 := by decide +kernel
      change 0 < (seed 0 13).region.getD 3 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s13_r4
    · exact region_s13_r5
  · fin_cases r
    · exact region_s14_r0
    · exact region_s14_r1
    · exact region_s14_r2
    · have hz : (seed 0 14).region.getD 3 0 = 0 := by decide +kernel
      change 0 < (seed 0 14).region.getD 3 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s14_r4
    · exact region_s14_r5
  · fin_cases r
    · exact region_s15_r0
    · exact region_s15_r1
    · exact region_s15_r2
    · exact region_s15_r3
    · exact region_s15_r4
    · exact region_s15_r5
  · exact False.elim ((by decide +kernel : (seed 0 16).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 0 17).boundary ≠ []) hi)
  · fin_cases r
    · exact region_s18_r0
    · exact region_s18_r1
    · exact region_s18_r2
    · have hz : (seed 0 18).region.getD 3 0 = 0 := by decide +kernel
      change 0 < (seed 0 18).region.getD 3 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 0 18).region.getD 4 0 = 0 := by decide +kernel
      change 0 < (seed 0 18).region.getD 4 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 0 18).region.getD 5 0 = 0 := by decide +kernel
      change 0 < (seed 0 18).region.getD 5 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
  · fin_cases r
    · exact region_s19_r0
    · exact region_s19_r1
    · exact region_s19_r2
    · exact region_s19_r3
    · have hz : (seed 0 19).region.getD 4 0 = 0 := by decide +kernel
      change 0 < (seed 0 19).region.getD 4 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 0 19).region.getD 5 0 = 0 := by decide +kernel
      change 0 < (seed 0 19).region.getD 5 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
  · fin_cases r
    · have hz : (seed 0 20).region.getD 0 0 = 0 := by decide +kernel
      change 0 < (seed 0 20).region.getD 0 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 0 20).region.getD 1 0 = 0 := by decide +kernel
      change 0 < (seed 0 20).region.getD 1 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s20_r2
    · exact region_s20_r3
    · exact region_s20_r4
    · exact region_s20_r5
  · fin_cases r
    · exact region_s21_r0
    · exact region_s21_r1
    · exact region_s21_r2
    · exact region_s21_r3
    · exact region_s21_r4
    · exact region_s21_r5
  · fin_cases r
    · exact region_s22_r0
    · exact region_s22_r1
    · have hz : (seed 0 22).region.getD 2 0 = 0 := by decide +kernel
      change 0 < (seed 0 22).region.getD 2 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s22_r3
    · exact region_s22_r4
    · exact region_s22_r5
  · exact False.elim ((by decide +kernel : (seed 0 23).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 0 24).boundary ≠ []) hi)
  · fin_cases r
    · exact region_s25_r0
    · exact region_s25_r1
    · exact region_s25_r2
    · have hz : (seed 0 25).region.getD 3 0 = 0 := by decide +kernel
      change 0 < (seed 0 25).region.getD 3 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 0 25).region.getD 4 0 = 0 := by decide +kernel
      change 0 < (seed 0 25).region.getD 4 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 0 25).region.getD 5 0 = 0 := by decide +kernel
      change 0 < (seed 0 25).region.getD 5 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
  · fin_cases r
    · exact region_s26_r0
    · exact region_s26_r1
    · have hz : (seed 0 26).region.getD 2 0 = 0 := by decide +kernel
      change 0 < (seed 0 26).region.getD 2 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 0 26).region.getD 3 0 = 0 := by decide +kernel
      change 0 < (seed 0 26).region.getD 3 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s26_r4
    · exact region_s26_r5
  · fin_cases r
    · exact region_s27_r0
    · exact region_s27_r1
    · exact region_s27_r2
    · exact region_s27_r3
    · have hz : (seed 0 27).region.getD 4 0 = 0 := by decide +kernel
      change 0 < (seed 0 27).region.getD 4 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 0 27).region.getD 5 0 = 0 := by decide +kernel
      change 0 < (seed 0 27).region.getD 5 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
  · fin_cases r
    · exact region_s28_r0
    · exact region_s28_r1
    · have hz : (seed 0 28).region.getD 2 0 = 0 := by decide +kernel
      change 0 < (seed 0 28).region.getD 2 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 0 28).region.getD 3 0 = 0 := by decide +kernel
      change 0 < (seed 0 28).region.getD 3 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s28_r4
    · have hz : (seed 0 28).region.getD 5 0 = 0 := by decide +kernel
      change 0 < (seed 0 28).region.getD 5 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
  · exact False.elim ((by decide +kernel : (seed 0 29).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 0 30).boundary ≠ []) hi)
  · fin_cases r
    · have hz : (seed 0 31).region.getD 0 0 = 0 := by decide +kernel
      change 0 < (seed 0 31).region.getD 0 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 0 31).region.getD 1 0 = 0 := by decide +kernel
      change 0 < (seed 0 31).region.getD 1 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 0 31).region.getD 2 0 = 0 := by decide +kernel
      change 0 < (seed 0 31).region.getD 2 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s31_r3
    · exact region_s31_r4
    · exact region_s31_r5
  · fin_cases r
    · exact region_s32_r0
    · exact region_s32_r1
    · exact region_s32_r2
    · have hz : (seed 0 32).region.getD 3 0 = 0 := by decide +kernel
      change 0 < (seed 0 32).region.getD 3 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s32_r4
    · have hz : (seed 0 32).region.getD 5 0 = 0 := by decide +kernel
      change 0 < (seed 0 32).region.getD 5 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
  · fin_cases r
    · have hz : (seed 0 33).region.getD 0 0 = 0 := by decide +kernel
      change 0 < (seed 0 33).region.getD 0 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 0 33).region.getD 1 0 = 0 := by decide +kernel
      change 0 < (seed 0 33).region.getD 1 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s33_r2
    · exact region_s33_r3
    · have hz : (seed 0 33).region.getD 4 0 = 0 := by decide +kernel
      change 0 < (seed 0 33).region.getD 4 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s33_r5
  · exact False.elim ((by decide +kernel : (seed 0 34).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 0 35).boundary ≠ []) hi)
  · fin_cases r
    · exact region_s36_r0
    · have hz : (seed 0 36).region.getD 1 0 = 0 := by decide +kernel
      change 0 < (seed 0 36).region.getD 1 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s36_r2
    · exact region_s36_r3
    · exact region_s36_r4
    · exact region_s36_r5
  · fin_cases r
    · have hz : (seed 0 37).region.getD 0 0 = 0 := by decide +kernel
      change 0 < (seed 0 37).region.getD 0 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s37_r1
    · exact region_s37_r2
    · exact region_s37_r3
    · exact region_s37_r4
    · exact region_s37_r5
  · exact False.elim ((by decide +kernel : (seed 0 38).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 0 39).boundary ≠ []) hi)
  · fin_cases r
    · exact region_s40_r0
    · exact region_s40_r1
    · exact region_s40_r2
    · exact region_s40_r3
    · exact region_s40_r4
    · exact region_s40_r5
  · exact False.elim ((by decide +kernel : (seed 0 41).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 0 42).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 0 43).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 0 44).boundary ≠ []) hi)


#print axioms solution
