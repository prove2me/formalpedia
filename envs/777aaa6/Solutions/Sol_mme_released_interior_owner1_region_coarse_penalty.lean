-- Prove2me | solution 1 for mme_released_interior_owner1_region_coarse_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T07:19:12.084831+00:00
-- url     : https://prove2.me/submissions/ea190110-871f-4635-bac6-effd40ceea55

import Theorems.Thm_mme_rational_coarse_penalty_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.RecursiveThinSplit MME.ReleasedInterior

private def alphaQ_s10_r0 (c : MME.ReleasedInterior.Split 10) : ℚ :=
  (splitWeight 1 10 0 c : ℚ) / 1000000000000

private def jointExponent_s10_r0 (c : MME.ReleasedInterior.Split 10) : ℕ :=
  [1, 3, 3, 1].getD ((seed 1 10).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s10_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 10 => c.val 0)
        (fun c => (splitWeight 1 10 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 10 => (splitWeight 1 10 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 10) : 0 ≤ alphaQ_s10_r0 c := by
    unfold alphaQ_s10_r0
    positivity
  have hprob : ∑ c, alphaQ_s10_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500384212282,499615787718,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500455156136,499544843864,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 1 10 1 c : ℚ) / 1000000000000

private def jointExponent_s10_r1 (c : MME.ReleasedInterior.Split 10) : ℕ :=
  [1, 3, 3, 1].getD ((seed 1 10).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s10_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 10 => c.val 0)
        (fun c => (splitWeight 1 10 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 10 => (splitWeight 1 10 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 10) : 0 ≤ alphaQ_s10_r1 c := by
    unfold alphaQ_s10_r1
    positivity
  have hprob : ∑ c, alphaQ_s10_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500352687041,499647312959,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500417355348,499582644652,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 1 10 2 c : ℚ) / 1000000000000

private def jointExponent_s10_r2 (c : MME.ReleasedInterior.Split 10) : ℕ :=
  [1, 3, 3, 1].getD ((seed 1 10).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s10_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 10 => c.val 0)
        (fun c => (splitWeight 1 10 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 10 => (splitWeight 1 10 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 10) : 0 ≤ alphaQ_s10_r2 c := by
    unfold alphaQ_s10_r2
    positivity
  have hprob : ∑ c, alphaQ_s10_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500390361682,499609638318,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500463901339,499536098661,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 1 10 3 c : ℚ) / 1000000000000

private def jointExponent_s10_r3 (c : MME.ReleasedInterior.Split 10) : ℕ :=
  [1, 3, 3, 1].getD ((seed 1 10).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s10_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 10 => c.val 0)
        (fun c => (splitWeight 1 10 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 10 => (splitWeight 1 10 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 10) : 0 ≤ alphaQ_s10_r3 c := by
    unfold alphaQ_s10_r3
    positivity
  have hprob : ∑ c, alphaQ_s10_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500387961342,499612038658,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500466121543,499533878457,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 1 10 4 c : ℚ) / 1000000000000

private def jointExponent_s10_r4 (c : MME.ReleasedInterior.Split 10) : ℕ :=
  [1, 3, 3, 1].getD ((seed 1 10).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s10_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 10 => c.val 0)
        (fun c => (splitWeight 1 10 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 10 => (splitWeight 1 10 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 10) : 0 ≤ alphaQ_s10_r4 c := by
    unfold alphaQ_s10_r4
    positivity
  have hprob : ∑ c, alphaQ_s10_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500352467799,499647532201,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500417757887,499582242113,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 1 10 5 c : ℚ) / 1000000000000

private def jointExponent_s10_r5 (c : MME.ReleasedInterior.Split 10) : ℕ :=
  [1, 3, 3, 1].getD ((seed 1 10).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s10_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 10 => c.val 0)
        (fun c => (splitWeight 1 10 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 10 => (splitWeight 1 10 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 10) : 0 ≤ alphaQ_s10_r5 c := by
    unfold alphaQ_s10_r5
    positivity
  have hprob : ∑ c, alphaQ_s10_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500381593219,499618406781,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500458025957,499541974043,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s11_r1 (c : MME.ReleasedInterior.Split 11) : ℚ :=
  (splitWeight 1 11 1 c : ℚ) / 1000000000000

private def jointExponent_s11_r1 (c : MME.ReleasedInterior.Split 11) : ℕ :=
  [3, 2, 7, 7, 2, 3].getD ((seed 1 11).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s11_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 11 => c.val 0)
        (fun c => (splitWeight 1 11 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 11 => (splitWeight 1 11 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 11) : 0 ≤ alphaQ_s11_r1 c := by
    unfold alphaQ_s11_r1
    positivity
  have hprob : ∑ c, alphaQ_s11_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000013737,499999986263,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,6589715822,493410288809,493410244559,6589750810] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s11_r1 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![1,1,0,0,0] ![1,1,40,40,40] ![40,7,1,1,7] jointExponent_s11_r1 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 11 => c.val 0)
        (fun c => (alphaQ_s11_r1 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s11_r1 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s11_r1, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s11_r4 (c : MME.ReleasedInterior.Split 11) : ℚ :=
  (splitWeight 1 11 4 c : ℚ) / 1000000000000

private def jointExponent_s11_r4 (c : MME.ReleasedInterior.Split 11) : ℕ :=
  [3, 2, 7, 7, 2, 3].getD ((seed 1 11).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s11_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 11 => c.val 0)
        (fun c => (splitWeight 1 11 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 11 => (splitWeight 1 11 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 11) : 0 ≤ alphaQ_s11_r4 c := by
    unfold alphaQ_s11_r4
    positivity
  have hprob : ∑ c, alphaQ_s11_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000005665,499999994335,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,6613252253,493386738679,493386779306,6613229762] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s11_r4 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![1,1,0,0,0] ![1,1,40,40,40] ![40,7,1,1,7] jointExponent_s11_r4 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 11 => c.val 0)
        (fun c => (alphaQ_s11_r4 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s11_r4 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s11_r4, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s11_r5 (c : MME.ReleasedInterior.Split 11) : ℚ :=
  (splitWeight 1 11 5 c : ℚ) / 1000000000000

private def jointExponent_s11_r5 (c : MME.ReleasedInterior.Split 11) : ℕ :=
  [3, 2, 7, 7, 2, 3].getD ((seed 1 11).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s11_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 11 => c.val 0)
        (fun c => (splitWeight 1 11 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 11 => (splitWeight 1 11 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 11) : 0 ≤ alphaQ_s11_r5 c := by
    unfold alphaQ_s11_r5
    positivity
  have hprob : ∑ c, alphaQ_s11_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000009833,499999990167,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,6635109951,493364875432,493364929205,6635085412] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s11_r5 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![1,1,0,0,0] ![1,1,40,40,40] ![40,7,1,1,7] jointExponent_s11_r5 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 11 => c.val 0)
        (fun c => (alphaQ_s11_r5 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s11_r5 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s11_r5, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s12_r1 (c : MME.ReleasedInterior.Split 12) : ℚ :=
  (splitWeight 1 12 1 c : ℚ) / 1000000000000

private def jointExponent_s12_r1 (c : MME.ReleasedInterior.Split 12) : ℕ :=
  [6, 1, 4, 12, 12, 4, 1, 6].getD ((seed 1 12).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s12_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 12 => c.val 0)
        (fun c => (splitWeight 1 12 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 12 => (splitWeight 1 12 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 12) : 0 ≤ alphaQ_s12_r1 c := by
    unfold alphaQ_s12_r1
    positivity
  have hprob : ∑ c, alphaQ_s12_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999797377,500000202623,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![326253823,73590113707,852167169883,73590151441,326311146] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s12_r1 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![1,1,0,0,0] ![1,1,40,40,40] ![12,4,0,4,12] jointExponent_s12_r1 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 12 => c.val 0)
        (fun c => (alphaQ_s12_r1 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s12_r1 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s12_r1, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s12_r4 (c : MME.ReleasedInterior.Split 12) : ℚ :=
  (splitWeight 1 12 4 c : ℚ) / 1000000000000

private def jointExponent_s12_r4 (c : MME.ReleasedInterior.Split 12) : ℕ :=
  [6, 1, 4, 12, 12, 4, 1, 6].getD ((seed 1 12).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s12_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 12 => c.val 0)
        (fun c => (splitWeight 1 12 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 12 => (splitWeight 1 12 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 12) : 0 ≤ alphaQ_s12_r4 c := by
    unfold alphaQ_s12_r4
    positivity
  have hprob : ∑ c, alphaQ_s12_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000031102,499999968898,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![323535069,73595515374,852161934270,73595507713,323507574] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s12_r4 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![1,1,0,0,0] ![1,1,40,40,40] ![12,4,0,4,12] jointExponent_s12_r4 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 12 => c.val 0)
        (fun c => (alphaQ_s12_r4 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s12_r4 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s12_r4, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s12_r5 (c : MME.ReleasedInterior.Split 12) : ℚ :=
  (splitWeight 1 12 5 c : ℚ) / 1000000000000

private def jointExponent_s12_r5 (c : MME.ReleasedInterior.Split 12) : ℕ :=
  [6, 1, 4, 12, 12, 4, 1, 6].getD ((seed 1 12).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s12_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 12 => c.val 0)
        (fun c => (splitWeight 1 12 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 12 => (splitWeight 1 12 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 12) : 0 ≤ alphaQ_s12_r5 c := by
    unfold alphaQ_s12_r5
    positivity
  have hprob : ∑ c, alphaQ_s12_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000010472,499999989528,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![325717736,70613285051,858122014759,70613313909,325668545] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s12_r5 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![1,1,0,0,0] ![1,1,40,40,40] ![12,4,0,4,12] jointExponent_s12_r5 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 12 => c.val 0)
        (fun c => (alphaQ_s12_r5 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s12_r5 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s12_r5, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s13_r0 (c : MME.ReleasedInterior.Split 13) : ℚ :=
  (splitWeight 1 13 0 c : ℚ) / 1000000000000

private def jointExponent_s13_r0 (c : MME.ReleasedInterior.Split 13) : ℕ :=
  [12, 4, 1, 6, 6, 1, 4, 12].getD ((seed 1 13).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s13_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 13 => c.val 0)
        (fun c => (splitWeight 1 13 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 13 => (splitWeight 1 13 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 13) : 0 ≤ alphaQ_s13_r0 c := by
    unfold alphaQ_s13_r0
    positivity
  have hprob : ∑ c, alphaQ_s13_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000039438,499999960562,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![327283836,77708251885,843928949194,77708231897,327283188] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s13_r0 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![1,1,0,0,0] ![1,1,40,40,40] ![12,4,0,4,12] jointExponent_s13_r0 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 13 => c.val 0)
        (fun c => (alphaQ_s13_r0 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s13_r0 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s13_r0, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s13_r2 (c : MME.ReleasedInterior.Split 13) : ℚ :=
  (splitWeight 1 13 2 c : ℚ) / 1000000000000

private def jointExponent_s13_r2 (c : MME.ReleasedInterior.Split 13) : ℕ :=
  [12, 4, 1, 6, 6, 1, 4, 12].getD ((seed 1 13).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s13_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 13 => c.val 0)
        (fun c => (splitWeight 1 13 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 13 => (splitWeight 1 13 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 13) : 0 ≤ alphaQ_s13_r2 c := by
    unfold alphaQ_s13_r2
    positivity
  have hprob : ∑ c, alphaQ_s13_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000061297,499999938703,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![325657038,77662452452,844023813378,77662426568,325650564] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s13_r2 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![1,1,0,0,0] ![1,1,40,40,40] ![12,4,0,4,12] jointExponent_s13_r2 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 13 => c.val 0)
        (fun c => (alphaQ_s13_r2 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s13_r2 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s13_r2, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s13_r3 (c : MME.ReleasedInterior.Split 13) : ℚ :=
  (splitWeight 1 13 3 c : ℚ) / 1000000000000

private def jointExponent_s13_r3 (c : MME.ReleasedInterior.Split 13) : ℕ :=
  [12, 4, 1, 6, 6, 1, 4, 12].getD ((seed 1 13).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s13_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 13 => c.val 0)
        (fun c => (splitWeight 1 13 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 13 => (splitWeight 1 13 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 13) : 0 ≤ alphaQ_s13_r3 c := by
    unfold alphaQ_s13_r3
    positivity
  have hprob : ∑ c, alphaQ_s13_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000014162,499999985838,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![323992225,74866107444,849619810325,74866100863,323989143] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s13_r3 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![1,1,0,0,0] ![1,1,40,40,40] ![12,4,0,4,12] jointExponent_s13_r3 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 13 => c.val 0)
        (fun c => (alphaQ_s13_r3 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s13_r3 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s13_r3, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s14_r0 (c : MME.ReleasedInterior.Split 14) : ℚ :=
  (splitWeight 1 14 0 c : ℚ) / 1000000000000

private def jointExponent_s14_r0 (c : MME.ReleasedInterior.Split 14) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 1 14).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s14_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 14 => c.val 0)
        (fun c => (splitWeight 1 14 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 14 => (splitWeight 1 14 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 14) : 0 ≤ alphaQ_s14_r0 c := by
    unfold alphaQ_s14_r0
    positivity
  have hprob : ∑ c, alphaQ_s14_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000006605,499999993395,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,7073347073,492926663282,492926625840,7073363805] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 1 14 1 c : ℚ) / 1000000000000

private def jointExponent_s14_r1 (c : MME.ReleasedInterior.Split 14) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 1 14).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s14_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 14 => c.val 0)
        (fun c => (splitWeight 1 14 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 14 => (splitWeight 1 14 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 14) : 0 ≤ alphaQ_s14_r1 c := by
    unfold alphaQ_s14_r1
    positivity
  have hprob : ∑ c, alphaQ_s14_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000085412,499999914588,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,7184458001,492815471248,492815586022,7184484729] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 1 14 2 c : ℚ) / 1000000000000

private def jointExponent_s14_r2 (c : MME.ReleasedInterior.Split 14) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 1 14).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s14_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 14 => c.val 0)
        (fun c => (splitWeight 1 14 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 14 => (splitWeight 1 14 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 14) : 0 ≤ alphaQ_s14_r2 c := by
    unfold alphaQ_s14_r2
    positivity
  have hprob : ∑ c, alphaQ_s14_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000010298,499999989702,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,7073922898,492926081615,492926030241,7073965246] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s14_r3 (c : MME.ReleasedInterior.Split 14) : ℚ :=
  (splitWeight 1 14 3 c : ℚ) / 1000000000000

private def jointExponent_s14_r3 (c : MME.ReleasedInterior.Split 14) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 1 14).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s14_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 14 => c.val 0)
        (fun c => (splitWeight 1 14 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 14 => (splitWeight 1 14 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 14) : 0 ≤ alphaQ_s14_r3 c := by
    unfold alphaQ_s14_r3
    positivity
  have hprob : ∑ c, alphaQ_s14_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000006806,499999993194,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,7037613445,492962390530,492962369633,7037626392] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s14_r3 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![1,1,0,0,0] ![1,1,40,40,40] ![40,7,1,1,7] jointExponent_s14_r3 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 14 => c.val 0)
        (fun c => (alphaQ_s14_r3 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s14_r3 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s14_r3, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s14_r4 (c : MME.ReleasedInterior.Split 14) : ℚ :=
  (splitWeight 1 14 4 c : ℚ) / 1000000000000

private def jointExponent_s14_r4 (c : MME.ReleasedInterior.Split 14) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 1 14).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s14_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 14 => c.val 0)
        (fun c => (splitWeight 1 14 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 14 => (splitWeight 1 14 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 14) : 0 ≤ alphaQ_s14_r4 c := by
    unfold alphaQ_s14_r4
    positivity
  have hprob : ∑ c, alphaQ_s14_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000098119,499999901881,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,7154458383,492845497089,492845438457,7154606071] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s15_r0 (c : MME.ReleasedInterior.Split 15) : ℚ :=
  (splitWeight 1 15 0 c : ℚ) / 1000000000000

private def jointExponent_s15_r0 (c : MME.ReleasedInterior.Split 15) : ℕ :=
  [3, 1, 1, 3].getD ((seed 1 15).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s15_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 15 => c.val 0)
        (fun c => (splitWeight 1 15 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 15 => (splitWeight 1 15 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 15) : 0 ≤ alphaQ_s15_r0 c := by
    unfold alphaQ_s15_r0
    positivity
  have hprob : ∑ c, alphaQ_s15_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999714740,500000285260,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999786211,500000213789,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 1 15 1 c : ℚ) / 1000000000000

private def jointExponent_s15_r1 (c : MME.ReleasedInterior.Split 15) : ℕ :=
  [3, 1, 1, 3].getD ((seed 1 15).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s15_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 15 => c.val 0)
        (fun c => (splitWeight 1 15 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 15 => (splitWeight 1 15 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 15) : 0 ≤ alphaQ_s15_r1 c := by
    unfold alphaQ_s15_r1
    positivity
  have hprob : ∑ c, alphaQ_s15_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499716923272,500283076728,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500146854074,499853145926,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 1 15 2 c : ℚ) / 1000000000000

private def jointExponent_s15_r2 (c : MME.ReleasedInterior.Split 15) : ℕ :=
  [3, 1, 1, 3].getD ((seed 1 15).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s15_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 15 => c.val 0)
        (fun c => (splitWeight 1 15 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 15 => (splitWeight 1 15 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 15) : 0 ≤ alphaQ_s15_r2 c := by
    unfold alphaQ_s15_r2
    positivity
  have hprob : ∑ c, alphaQ_s15_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499998573069,500001426931,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000393301,499999606699,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 1 15 3 c : ℚ) / 1000000000000

private def jointExponent_s15_r3 (c : MME.ReleasedInterior.Split 15) : ℕ :=
  [3, 1, 1, 3].getD ((seed 1 15).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s15_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 15 => c.val 0)
        (fun c => (splitWeight 1 15 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 15 => (splitWeight 1 15 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 15) : 0 ≤ alphaQ_s15_r3 c := by
    unfold alphaQ_s15_r3
    positivity
  have hprob : ∑ c, alphaQ_s15_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500138968368,499861031632,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499926492803,500073507197,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 1 15 4 c : ℚ) / 1000000000000

private def jointExponent_s15_r4 (c : MME.ReleasedInterior.Split 15) : ℕ :=
  [3, 1, 1, 3].getD ((seed 1 15).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s15_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 15 => c.val 0)
        (fun c => (splitWeight 1 15 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 15 => (splitWeight 1 15 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 15) : 0 ≤ alphaQ_s15_r4 c := by
    unfold alphaQ_s15_r4
    positivity
  have hprob : ∑ c, alphaQ_s15_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000742381,499999257619,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999234345,500000765655,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 1 15 5 c : ℚ) / 1000000000000

private def jointExponent_s15_r5 (c : MME.ReleasedInterior.Split 15) : ℕ :=
  [3, 1, 1, 3].getD ((seed 1 15).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s15_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 15 => c.val 0)
        (fun c => (splitWeight 1 15 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 15 => (splitWeight 1 15 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 15) : 0 ≤ alphaQ_s15_r5 c := by
    unfold alphaQ_s15_r5
    positivity
  have hprob : ∑ c, alphaQ_s15_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000721484,499999278516,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999237273,500000762727,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 1 18 0 c : ℚ) / 1000000000000

private def jointExponent_s18_r0 (c : MME.ReleasedInterior.Split 18) : ℕ :=
  [3, 7, 2, 2, 7, 3].getD ((seed 1 18).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s18_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 18 => c.val 0)
        (fun c => (splitWeight 1 18 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 18 => (splitWeight 1 18 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 18) : 0 ≤ alphaQ_s18_r0 c := by
    unfold alphaQ_s18_r0
    positivity
  have hprob : ∑ c, alphaQ_s18_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000007807,499999992193,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,6634354391,493365651593,493365580737,6634413279] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 1 18 1 c : ℚ) / 1000000000000

private def jointExponent_s18_r1 (c : MME.ReleasedInterior.Split 18) : ℕ :=
  [3, 7, 2, 2, 7, 3].getD ((seed 1 18).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s18_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 18 => c.val 0)
        (fun c => (splitWeight 1 18 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 18 => (splitWeight 1 18 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 18) : 0 ≤ alphaQ_s18_r1 c := by
    unfold alphaQ_s18_r1
    positivity
  have hprob : ∑ c, alphaQ_s18_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000013089,499999986911,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,6613023358,493386985147,493386881079,6613110416] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s18_r4 (c : MME.ReleasedInterior.Split 18) : ℚ :=
  (splitWeight 1 18 4 c : ℚ) / 1000000000000

private def jointExponent_s18_r4 (c : MME.ReleasedInterior.Split 18) : ℕ :=
  [3, 7, 2, 2, 7, 3].getD ((seed 1 18).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s18_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 18 => c.val 0)
        (fun c => (splitWeight 1 18 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 18 => (splitWeight 1 18 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 18) : 0 ≤ alphaQ_s18_r4 c := by
    unfold alphaQ_s18_r4
    positivity
  have hprob : ∑ c, alphaQ_s18_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999992089,500000007911,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,6589736256,493410245075,493410332347,6589686322] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s18_r4 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![3,1,3,0,0] ![1,1,40,40,40] ![40,7,1,1,7] jointExponent_s18_r4 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 18 => c.val 0)
        (fun c => (alphaQ_s18_r4 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s18_r4 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s18_r4, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s19_r0 (c : MME.ReleasedInterior.Split 19) : ℚ :=
  (splitWeight 1 19 0 c : ℚ) / 1000000000000

private def jointExponent_s19_r0 (c : MME.ReleasedInterior.Split 19) : ℕ :=
  [3, 5, 12, 5, 1, 5, 12, 5, 3].getD ((seed 1 19).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s19_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 19 => c.val 0)
        (fun c => (splitWeight 1 19 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 19 => (splitWeight 1 19 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 19) : 0 ≤ alphaQ_s19_r0 c := by
    unfold alphaQ_s19_r0
    positivity
  have hprob : ∑ c, alphaQ_s19_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![180467079900,639065825375,180467094725,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![318870682,71768610902,855825092111,71768525538,318900767] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 1 19 1 c : ℚ) / 1000000000000

private def jointExponent_s19_r1 (c : MME.ReleasedInterior.Split 19) : ℕ :=
  [3, 5, 12, 5, 1, 5, 12, 5, 3].getD ((seed 1 19).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s19_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 19 => c.val 0)
        (fun c => (splitWeight 1 19 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 19 => (splitWeight 1 19 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 19) : 0 ≤ alphaQ_s19_r1 c := by
    unfold alphaQ_s19_r1
    positivity
  have hprob : ∑ c, alphaQ_s19_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![183323962708,633352101157,183323936135,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![319699148,72983647801,853393311037,72983585187,319756827] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s19_r4 (c : MME.ReleasedInterior.Split 19) : ℚ :=
  (splitWeight 1 19 4 c : ℚ) / 1000000000000

private def jointExponent_s19_r4 (c : MME.ReleasedInterior.Split 19) : ℕ :=
  [3, 5, 12, 5, 1, 5, 12, 5, 3].getD ((seed 1 19).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s19_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 19 => c.val 0)
        (fun c => (splitWeight 1 19 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 19 => (splitWeight 1 19 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 19) : 0 ≤ alphaQ_s19_r4 c := by
    unfold alphaQ_s19_r4
    positivity
  have hprob : ∑ c, alphaQ_s19_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![183346350728,633307328478,183346320794,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![319650234,72980360190,853399984436,72980289369,319715771] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s19_r4 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![3,1,3,0,0] ![3,1,3,40,40] ![12,4,0,4,12] jointExponent_s19_r4 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 19 => c.val 0)
        (fun c => (alphaQ_s19_r4 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s19_r4 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s19_r4, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s19_r5 (c : MME.ReleasedInterior.Split 19) : ℚ :=
  (splitWeight 1 19 5 c : ℚ) / 1000000000000

private def jointExponent_s19_r5 (c : MME.ReleasedInterior.Split 19) : ℕ :=
  [3, 5, 12, 5, 1, 5, 12, 5, 3].getD ((seed 1 19).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s19_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 19 => c.val 0)
        (fun c => (splitWeight 1 19 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 19 => (splitWeight 1 19 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 19) : 0 ≤ alphaQ_s19_r5 c := by
    unfold alphaQ_s19_r5
    positivity
  have hprob : ∑ c, alphaQ_s19_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![180483265368,639033458960,180483275672,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![318877179,71767208628,855827865635,71767150846,318897712] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s19_r5 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![3,1,3,0,0] ![3,1,3,40,40] ![12,4,0,4,12] jointExponent_s19_r5 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 19 => c.val 0)
        (fun c => (alphaQ_s19_r5 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s19_r5 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s19_r5, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s20_r2 (c : MME.ReleasedInterior.Split 20) : ℚ :=
  (splitWeight 1 20 2 c : ℚ) / 1000000000000

private def jointExponent_s20_r2 (c : MME.ReleasedInterior.Split 20) : ℕ :=
  [6, 3, 7, 9, 2, 2, 9, 7, 3, 6].getD ((seed 1 20).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s20_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 20 => c.val 0)
        (fun c => (splitWeight 1 20 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 20 => (splitWeight 1 20 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 20) : 0 ≤ alphaQ_s20_r2 c := by
    unfold alphaQ_s20_r2
    positivity
  have hprob : ∑ c, alphaQ_s20_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![13655215002,486344918498,486345453825,13654412675,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![12669918953,487329926899,487329390478,12670763670,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 1 20 3 c : ℚ) / 1000000000000

private def jointExponent_s20_r3 (c : MME.ReleasedInterior.Split 20) : ℕ :=
  [7, 3, 7, 9, 2, 2, 9, 7, 3, 7].getD ((seed 1 20).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s20_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 20 => c.val 0)
        (fun c => (splitWeight 1 20 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 20 => (splitWeight 1 20 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 20) : 0 ≤ alphaQ_s20_r3 c := by
    unfold alphaQ_s20_r3
    positivity
  have hprob : ∑ c, alphaQ_s20_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![13042072666,486958049340,486958580935,13041297059,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![12231537655,487768343963,487767778293,12232340089,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 1 20 4 c : ℚ) / 1000000000000

private def jointExponent_s20_r4 (c : MME.ReleasedInterior.Split 20) : ℕ :=
  [7, 3, 6, 9, 2, 2, 9, 6, 3, 7].getD ((seed 1 20).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s20_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 20 => c.val 0)
        (fun c => (splitWeight 1 20 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 20 => (splitWeight 1 20 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 20) : 0 ≤ alphaQ_s20_r4 c := by
    unfold alphaQ_s20_r4
    positivity
  have hprob : ∑ c, alphaQ_s20_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![12738896706,487261133415,487261212771,12738757108,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![13573029650,486426949476,486426845321,13573175553,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 1 20 5 c : ℚ) / 1000000000000

private def jointExponent_s20_r5 (c : MME.ReleasedInterior.Split 20) : ℕ :=
  [7, 3, 7, 9, 2, 2, 9, 7, 3, 7].getD ((seed 1 20).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s20_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 20 => c.val 0)
        (fun c => (splitWeight 1 20 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 20 => (splitWeight 1 20 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 20) : 0 ≤ alphaQ_s20_r5 c := by
    unfold alphaQ_s20_r5
    positivity
  have hprob : ∑ c, alphaQ_s20_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![12291065436,487708964003,487709075709,12290894852,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![12957266383,487042707264,487042585501,12957440852,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 1 21 0 c : ℚ) / 1000000000000

private def jointExponent_s21_r0 (c : MME.ReleasedInterior.Split 21) : ℕ :=
  [12, 5, 3, 5, 1, 5, 3, 5, 12].getD ((seed 1 21).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s21_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 21 => c.val 0)
        (fun c => (splitWeight 1 21 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 21 => (splitWeight 1 21 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 21) : 0 ≤ alphaQ_s21_r0 c := by
    unfold alphaQ_s21_r0
    positivity
  have hprob : ∑ c, alphaQ_s21_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![183366966262,633266063095,183366970643,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![333448562,77544029340,844245043808,77544032837,333445453] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 1 21 1 c : ℚ) / 1000000000000

private def jointExponent_s21_r1 (c : MME.ReleasedInterior.Split 21) : ℕ :=
  [12, 5, 3, 5, 1, 5, 3, 5, 12].getD ((seed 1 21).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s21_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 21 => c.val 0)
        (fun c => (splitWeight 1 21 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 21 => (splitWeight 1 21 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 21) : 0 ≤ alphaQ_s21_r1 c := by
    unfold alphaQ_s21_r1
    positivity
  have hprob : ∑ c, alphaQ_s21_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![180495559093,639008881410,180495559497,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![328671728,76178909744,846984836044,76178909302,328673182] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 1 21 2 c : ℚ) / 1000000000000

private def jointExponent_s21_r2 (c : MME.ReleasedInterior.Split 21) : ℕ :=
  [12, 5, 3, 5, 1, 5, 3, 5, 12].getD ((seed 1 21).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s21_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 21 => c.val 0)
        (fun c => (splitWeight 1 21 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 21 => (splitWeight 1 21 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 21) : 0 ≤ alphaQ_s21_r2 c := by
    unfold alphaQ_s21_r2
    positivity
  have hprob : ∑ c, alphaQ_s21_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![333454320,77544422033,844244246759,77544423141,333453747] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![183434387216,633131228903,183434383881,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s21_r2 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![3,1,3,0,0] ![12,4,0,4,12] ![3,1,3,40,40] jointExponent_s21_r2 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 21 => c.val 0)
        (fun c => (alphaQ_s21_r2 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s21_r2 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s21_r2, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s21_r3 (c : MME.ReleasedInterior.Split 21) : ℚ :=
  (splitWeight 1 21 3 c : ℚ) / 1000000000000

private def jointExponent_s21_r3 (c : MME.ReleasedInterior.Split 21) : ℕ :=
  [12, 5, 3, 5, 1, 5, 3, 5, 12].getD ((seed 1 21).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s21_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 21 => c.val 0)
        (fun c => (splitWeight 1 21 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 21 => (splitWeight 1 21 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 21) : 0 ≤ alphaQ_s21_r3 c := by
    unfold alphaQ_s21_r3
    positivity
  have hprob : ∑ c, alphaQ_s21_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![328760343,76184472123,846973533455,76184476111,328757968] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![180583977406,638832046596,180583975998,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 1 21 4 c : ℚ) / 1000000000000

private def jointExponent_s21_r4 (c : MME.ReleasedInterior.Split 21) : ℕ :=
  [12, 5, 3, 5, 1, 5, 3, 5, 12].getD ((seed 1 21).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s21_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 21 => c.val 0)
        (fun c => (splitWeight 1 21 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 21 => (splitWeight 1 21 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 21) : 0 ≤ alphaQ_s21_r4 c := by
    unfold alphaQ_s21_r4
    positivity
  have hprob : ∑ c, alphaQ_s21_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![181625415600,636749165064,181625419336,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![328638390,76799026487,845744669952,76799026741,328638430] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s21_r4 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![3,1,3,0,0] ![3,1,3,40,40] ![12,4,0,4,12] jointExponent_s21_r4 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 21 => c.val 0)
        (fun c => (alphaQ_s21_r4 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s21_r4 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s21_r4, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s21_r5 (c : MME.ReleasedInterior.Split 21) : ℚ :=
  (splitWeight 1 21 5 c : ℚ) / 1000000000000

private def jointExponent_s21_r5 (c : MME.ReleasedInterior.Split 21) : ℕ :=
  [12, 5, 3, 5, 1, 5, 3, 5, 12].getD ((seed 1 21).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s21_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 21 => c.val 0)
        (fun c => (splitWeight 1 21 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 21 => (splitWeight 1 21 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 21) : 0 ≤ alphaQ_s21_r5 c := by
    unfold alphaQ_s21_r5
    positivity
  have hprob : ∑ c, alphaQ_s21_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![328772363,76801598005,845739259414,76801585462,328784756] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![181705292812,636589424903,181705282285,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 1 22 0 c : ℚ) / 1000000000000

private def jointExponent_s22_r0 (c : MME.ReleasedInterior.Split 22) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 1 22).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s22_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 22 => c.val 0)
        (fun c => (splitWeight 1 22 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 22 => (splitWeight 1 22 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 22) : 0 ≤ alphaQ_s22_r0 c := by
    unfold alphaQ_s22_r0
    positivity
  have hprob : ∑ c, alphaQ_s22_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7068612483,492931420859,492931203347,7068763311] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000030814,499999969186,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 1 22 1 c : ℚ) / 1000000000000

private def jointExponent_s22_r1 (c : MME.ReleasedInterior.Split 22) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 1 22).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s22_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 22 => c.val 0)
        (fun c => (splitWeight 1 22 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 22 => (splitWeight 1 22 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 22) : 0 ≤ alphaQ_s22_r1 c := by
    unfold alphaQ_s22_r1
    positivity
  have hprob : ∑ c, alphaQ_s22_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7031811052,492968225257,492967997746,7031965945] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000029486,499999970514,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s22_r2 (c : MME.ReleasedInterior.Split 22) : ℚ :=
  (splitWeight 1 22 2 c : ℚ) / 1000000000000

private def jointExponent_s22_r2 (c : MME.ReleasedInterior.Split 22) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 1 22).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s22_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 22 => c.val 0)
        (fun c => (splitWeight 1 22 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 22 => (splitWeight 1 22 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 22) : 0 ≤ alphaQ_s22_r2 c := by
    unfold alphaQ_s22_r2
    positivity
  have hprob : ∑ c, alphaQ_s22_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7067321571,492932712585,492932493367,7067472477] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000034440,499999965560,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s22_r2 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![3,1,3,0,0] ![40,7,1,1,7] ![1,1,40,40,40] jointExponent_s22_r2 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 22 => c.val 0)
        (fun c => (alphaQ_s22_r2 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s22_r2 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s22_r2, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s22_r3 (c : MME.ReleasedInterior.Split 22) : ℚ :=
  (splitWeight 1 22 3 c : ℚ) / 1000000000000

private def jointExponent_s22_r3 (c : MME.ReleasedInterior.Split 22) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 1 22).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s22_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 22 => c.val 0)
        (fun c => (splitWeight 1 22 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 22 => (splitWeight 1 22 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 22) : 0 ≤ alphaQ_s22_r3 c := by
    unfold alphaQ_s22_r3
    positivity
  have hprob : ∑ c, alphaQ_s22_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7168893917,492831116443,492830934280,7169055360] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000054458,499999945542,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s22_r5 (c : MME.ReleasedInterior.Split 22) : ℚ :=
  (splitWeight 1 22 5 c : ℚ) / 1000000000000

private def jointExponent_s22_r5 (c : MME.ReleasedInterior.Split 22) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 1 22).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s22_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 22 => c.val 0)
        (fun c => (splitWeight 1 22 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 22 => (splitWeight 1 22 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 22) : 0 ≤ alphaQ_s22_r5 c := by
    unfold alphaQ_s22_r5
    positivity
  have hprob : ∑ c, alphaQ_s22_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7150281250,492849740575,492849492933,7150485242] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000060110,499999939890,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 1 25 0 c : ℚ) / 1000000000000

private def jointExponent_s25_r0 (c : MME.ReleasedInterior.Split 25) : ℕ :=
  [6, 12, 1, 4, 4, 1, 12, 6].getD ((seed 1 25).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s25_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 25 => c.val 0)
        (fun c => (splitWeight 1 25 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 25 => (splitWeight 1 25 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 25) : 0 ≤ alphaQ_s25_r0 c := by
    unfold alphaQ_s25_r0
    positivity
  have hprob : ∑ c, alphaQ_s25_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999998173,500000001827,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![328162106,70625349050,858092975368,70625347661,328165815] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 1 25 1 c : ℚ) / 1000000000000

private def jointExponent_s25_r1 (c : MME.ReleasedInterior.Split 25) : ℕ :=
  [6, 12, 1, 4, 4, 1, 12, 6].getD ((seed 1 25).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s25_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 25 => c.val 0)
        (fun c => (splitWeight 1 25 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 25 => (splitWeight 1 25 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 25) : 0 ≤ alphaQ_s25_r1 c := by
    unfold alphaQ_s25_r1
    positivity
  have hprob : ∑ c, alphaQ_s25_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999981238,500000018762,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![325012709,73638407796,852073158538,73638403409,325017548] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s25_r4 (c : MME.ReleasedInterior.Split 25) : ℚ :=
  (splitWeight 1 25 4 c : ℚ) / 1000000000000

private def jointExponent_s25_r4 (c : MME.ReleasedInterior.Split 25) : ℕ :=
  [6, 12, 1, 4, 4, 1, 12, 6].getD ((seed 1 25).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s25_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 25 => c.val 0)
        (fun c => (splitWeight 1 25 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 25 => (splitWeight 1 25 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 25) : 0 ≤ alphaQ_s25_r4 c := by
    unfold alphaQ_s25_r4
    positivity
  have hprob : ∑ c, alphaQ_s25_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000010242,499999989758,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![328029303,73616890579,852110170841,73616882149,328027128] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s25_r4 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![6,1,1,6,0] ![1,1,40,40,40] ![12,4,0,4,12] jointExponent_s25_r4 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 25 => c.val 0)
        (fun c => (alphaQ_s25_r4 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s25_r4 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s25_r4, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s26_r0 (c : MME.ReleasedInterior.Split 26) : ℚ :=
  (splitWeight 1 26 0 c : ℚ) / 1000000000000

private def jointExponent_s26_r0 (c : MME.ReleasedInterior.Split 26) : ℕ :=
  [7, 9, 3, 2, 7, 7, 2, 3, 9, 7].getD ((seed 1 26).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s26_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 26 => c.val 0)
        (fun c => (splitWeight 1 26 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 26 => (splitWeight 1 26 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 26) : 0 ≤ alphaQ_s26_r0 c := by
    unfold alphaQ_s26_r0
    positivity
  have hprob : ∑ c, alphaQ_s26_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![12392503877,487607512028,487607538727,12392445368,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![12956258112,487043735587,487043670959,12956335342,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 1 26 1 c : ℚ) / 1000000000000

private def jointExponent_s26_r1 (c : MME.ReleasedInterior.Split 26) : ℕ :=
  [7, 9, 3, 2, 6, 6, 2, 3, 9, 7].getD ((seed 1 26).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s26_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 26 => c.val 0)
        (fun c => (splitWeight 1 26 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 26 => (splitWeight 1 26 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 26) : 0 ≤ alphaQ_s26_r1 c := by
    unfold alphaQ_s26_r1
    positivity
  have hprob : ∑ c, alphaQ_s26_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![12849270661,487150749892,487150781941,12849197506,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![13577411970,486422578302,486422508216,13577501512,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s26_r2 (c : MME.ReleasedInterior.Split 26) : ℚ :=
  (splitWeight 1 26 2 c : ℚ) / 1000000000000

private def jointExponent_s26_r2 (c : MME.ReleasedInterior.Split 26) : ℕ :=
  [7, 9, 3, 2, 7, 7, 2, 3, 9, 7].getD ((seed 1 26).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s26_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 26 => c.val 0)
        (fun c => (splitWeight 1 26 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 26 => (splitWeight 1 26 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 26) : 0 ≤ alphaQ_s26_r2 c := by
    unfold alphaQ_s26_r2
    positivity
  have hprob : ∑ c, alphaQ_s26_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![13161427209,486838578192,486838564291,13161430308,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![12245084107,487754919201,487754893682,12245103010,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s26_r2 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![6,1,1,6,0] ![6,1,1,6,40] ![6,1,1,6,40] jointExponent_s26_r2 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 26 => c.val 0)
        (fun c => (alphaQ_s26_r2 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s26_r2 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s26_r2, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s26_r3 (c : MME.ReleasedInterior.Split 26) : ℚ :=
  (splitWeight 1 26 3 c : ℚ) / 1000000000000

private def jointExponent_s26_r3 (c : MME.ReleasedInterior.Split 26) : ℕ :=
  [6, 9, 3, 2, 7, 7, 2, 3, 9, 6].getD ((seed 1 26).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s26_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 26 => c.val 0)
        (fun c => (splitWeight 1 26 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 26 => (splitWeight 1 26 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 26) : 0 ≤ alphaQ_s26_r3 c := by
    unfold alphaQ_s26_r3
    positivity
  have hprob : ∑ c, alphaQ_s26_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![13770744948,486229261256,486229242868,13770750928,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![12680196356,487319806051,487319787384,12680210209,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s26_r3 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![6,1,1,6,0] ![6,1,1,6,40] ![6,1,1,6,40] jointExponent_s26_r3 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 26 => c.val 0)
        (fun c => (alphaQ_s26_r3 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s26_r3 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s26_r3, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s27_r0 (c : MME.ReleasedInterior.Split 27) : ℚ :=
  (splitWeight 1 27 0 c : ℚ) / 1000000000000

private def jointExponent_s27_r0 (c : MME.ReleasedInterior.Split 27) : ℕ :=
  [9, 7, 6, 2, 3, 3, 2, 6, 7, 9].getD ((seed 1 27).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s27_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 27 => c.val 0)
        (fun c => (splitWeight 1 27 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 27 => (splitWeight 1 27 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 27) : 0 ≤ alphaQ_s27_r0 c := by
    unfold alphaQ_s27_r0
    positivity
  have hprob : ∑ c, alphaQ_s27_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![12851556744,487148443324,487148468547,12851531385,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![13661064171,486338929355,486338928197,13661078277,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 1 27 1 c : ℚ) / 1000000000000

private def jointExponent_s27_r1 (c : MME.ReleasedInterior.Split 27) : ℕ :=
  [9, 7, 7, 2, 3, 3, 2, 7, 7, 9].getD ((seed 1 27).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s27_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 27 => c.val 0)
        (fun c => (splitWeight 1 27 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 27 => (splitWeight 1 27 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 27) : 0 ≤ alphaQ_s27_r1 c := by
    unfold alphaQ_s27_r1
    positivity
  have hprob : ∑ c, alphaQ_s27_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![12403313313,487596688451,487596725170,12403273066,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![13040279625,486959709858,486959699462,13040311055,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s27_r4 (c : MME.ReleasedInterior.Split 27) : ℚ :=
  (splitWeight 1 27 4 c : ℚ) / 1000000000000

private def jointExponent_s27_r4 (c : MME.ReleasedInterior.Split 27) : ℕ :=
  [9, 7, 7, 2, 3, 3, 2, 7, 7, 9].getD ((seed 1 27).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s27_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 27 => c.val 0)
        (fun c => (splitWeight 1 27 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 27 => (splitWeight 1 27 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 27) : 0 ≤ alphaQ_s27_r4 c := by
    unfold alphaQ_s27_r4
    positivity
  have hprob : ∑ c, alphaQ_s27_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![13162967966,486837029554,486837045913,13162956567,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![12314089174,487685908104,487685905701,12314097021,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s27_r4 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![6,1,1,6,0] ![6,1,1,6,40] ![6,1,1,6,40] jointExponent_s27_r4 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 27 => c.val 0)
        (fun c => (alphaQ_s27_r4 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s27_r4 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s27_r4, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s27_r5 (c : MME.ReleasedInterior.Split 27) : ℚ :=
  (splitWeight 1 27 5 c : ℚ) / 1000000000000

private def jointExponent_s27_r5 (c : MME.ReleasedInterior.Split 27) : ℕ :=
  [9, 6, 7, 2, 3, 3, 2, 7, 6, 9].getD ((seed 1 27).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s27_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 27 => c.val 0)
        (fun c => (splitWeight 1 27 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 27 => (splitWeight 1 27 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 27) : 0 ≤ alphaQ_s27_r5 c := by
    unfold alphaQ_s27_r5
    positivity
  have hprob : ∑ c, alphaQ_s27_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![13775502253,486224497828,486224516908,13775483011,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![12750424765,487249569917,487249563169,12750442149,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s27_r5 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![6,1,1,6,0] ![6,1,1,6,40] ![6,1,1,6,40] jointExponent_s27_r5 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 27 => c.val 0)
        (fun c => (alphaQ_s27_r5 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s27_r5 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s27_r5, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s28_r0 (c : MME.ReleasedInterior.Split 28) : ℚ :=
  (splitWeight 1 28 0 c : ℚ) / 1000000000000

private def jointExponent_s28_r0 (c : MME.ReleasedInterior.Split 28) : ℕ :=
  [12, 6, 4, 1, 1, 4, 6, 12].getD ((seed 1 28).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s28_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 28 => c.val 0)
        (fun c => (splitWeight 1 28 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 28 => (splitWeight 1 28 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 28) : 0 ≤ alphaQ_s28_r0 c := by
    unfold alphaQ_s28_r0
    positivity
  have hprob : ∑ c, alphaQ_s28_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![328491781,77720289316,843902437000,77720291106,328490797] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999990647,500000009353,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 1 28 1 c : ℚ) / 1000000000000

private def jointExponent_s28_r1 (c : MME.ReleasedInterior.Split 28) : ℕ :=
  [12, 6, 4, 1, 1, 4, 6, 12].getD ((seed 1 28).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s28_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 28 => c.val 0)
        (fun c => (splitWeight 1 28 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 28 => (splitWeight 1 28 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 28) : 0 ≤ alphaQ_s28_r1 c := by
    unfold alphaQ_s28_r1
    positivity
  have hprob : ∑ c, alphaQ_s28_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![328253343,74877819242,849587854359,74877821598,328251458] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999997096,500000002904,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s28_r2 (c : MME.ReleasedInterior.Split 28) : ℚ :=
  (splitWeight 1 28 2 c : ℚ) / 1000000000000

private def jointExponent_s28_r2 (c : MME.ReleasedInterior.Split 28) : ℕ :=
  [12, 6, 4, 1, 1, 4, 6, 12].getD ((seed 1 28).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s28_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 28 => c.val 0)
        (fun c => (splitWeight 1 28 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 28 => (splitWeight 1 28 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 28) : 0 ≤ alphaQ_s28_r2 c := by
    unfold alphaQ_s28_r2
    positivity
  have hprob : ∑ c, alphaQ_s28_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![330518311,77755756346,843827452087,77755754767,330518489] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000000404,499999999596,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s28_r2 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![6,1,1,6,0] ![12,4,0,4,12] ![1,1,40,40,40] jointExponent_s28_r2 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 28 => c.val 0)
        (fun c => (alphaQ_s28_r2 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s28_r2 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s28_r2, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s31_r2 (c : MME.ReleasedInterior.Split 31) : ℚ :=
  (splitWeight 1 31 2 c : ℚ) / 1000000000000

private def jointExponent_s31_r2 (c : MME.ReleasedInterior.Split 31) : ℕ :=
  [12, 4, 6, 1, 1, 6, 4, 12].getD ((seed 1 31).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s31_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 31 => c.val 0)
        (fun c => (splitWeight 1 31 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 31 => (splitWeight 1 31 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 31) : 0 ≤ alphaQ_s31_r2 c := by
    unfold alphaQ_s31_r2
    positivity
  have hprob : ∑ c, alphaQ_s31_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![324684759,77741785126,843867068732,77741775199,324686184] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000014856,499999985144,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s31_r2 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![12,4,0,4,12] ![12,4,0,4,12] ![1,1,40,40,40] jointExponent_s31_r2 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 31 => c.val 0)
        (fun c => (alphaQ_s31_r2 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s31_r2 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s31_r2, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s31_r3 (c : MME.ReleasedInterior.Split 31) : ℚ :=
  (splitWeight 1 31 3 c : ℚ) / 1000000000000

private def jointExponent_s31_r3 (c : MME.ReleasedInterior.Split 31) : ℕ :=
  [12, 4, 6, 1, 1, 6, 4, 12].getD ((seed 1 31).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s31_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 31 => c.val 0)
        (fun c => (splitWeight 1 31 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 31 => (splitWeight 1 31 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 31) : 0 ≤ alphaQ_s31_r3 c := by
    unfold alphaQ_s31_r3
    positivity
  have hprob : ∑ c, alphaQ_s31_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![327531415,80461993523,838420975775,80461965032,327534255] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000045172,499999954828,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s31_r5 (c : MME.ReleasedInterior.Split 31) : ℚ :=
  (splitWeight 1 31 5 c : ℚ) / 1000000000000

private def jointExponent_s31_r5 (c : MME.ReleasedInterior.Split 31) : ℕ :=
  [12, 4, 6, 1, 1, 6, 4, 12].getD ((seed 1 31).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s31_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 31 => c.val 0)
        (fun c => (splitWeight 1 31 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 31 => (splitWeight 1 31 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 31) : 0 ≤ alphaQ_s31_r5 c := by
    unfold alphaQ_s31_r5
    positivity
  have hprob : ∑ c, alphaQ_s31_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![328723761,80536613320,838269335559,80536603518,328723842] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000015214,499999984786,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 1 32 0 c : ℚ) / 1000000000000

private def jointExponent_s32_r0 (c : MME.ReleasedInterior.Split 32) : ℕ :=
  [12, 5, 5, 3, 1, 3, 5, 5, 12].getD ((seed 1 32).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s32_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 32 => c.val 0)
        (fun c => (splitWeight 1 32 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 32 => (splitWeight 1 32 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 32) : 0 ≤ alphaQ_s32_r0 c := by
    unfold alphaQ_s32_r0
    positivity
  have hprob : ∑ c, alphaQ_s32_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![336160439,79861676318,839604329175,79861750656,336083412] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![181881241854,636237480120,181881278026,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s32_r0 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![12,4,0,4,12] ![12,4,0,4,12] ![3,1,3,40,40] jointExponent_s32_r0 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 32 => c.val 0)
        (fun c => (alphaQ_s32_r0 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s32_r0 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s32_r0, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s32_r1 (c : MME.ReleasedInterior.Split 32) : ℚ :=
  (splitWeight 1 32 1 c : ℚ) / 1000000000000

private def jointExponent_s32_r1 (c : MME.ReleasedInterior.Split 32) : ℕ :=
  [12, 5, 5, 3, 1, 3, 5, 5, 12].getD ((seed 1 32).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s32_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 32 => c.val 0)
        (fun c => (splitWeight 1 32 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 32 => (splitWeight 1 32 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 32) : 0 ≤ alphaQ_s32_r1 c := by
    unfold alphaQ_s32_r1
    positivity
  have hprob : ∑ c, alphaQ_s32_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![336085250,79861227076,839605379151,79861279991,336028532] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![181826362911,636347240662,181826396427,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s32_r1 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![12,4,0,4,12] ![12,4,0,4,12] ![3,1,3,40,40] jointExponent_s32_r1 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 32 => c.val 0)
        (fun c => (alphaQ_s32_r1 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s32_r1 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s32_r1, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s32_r2 (c : MME.ReleasedInterior.Split 32) : ℚ :=
  (splitWeight 1 32 2 c : ℚ) / 1000000000000

private def jointExponent_s32_r2 (c : MME.ReleasedInterior.Split 32) : ℕ :=
  [12, 5, 5, 3, 1, 3, 5, 5, 12].getD ((seed 1 32).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s32_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 32 => c.val 0)
        (fun c => (splitWeight 1 32 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 32 => (splitWeight 1 32 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 32) : 0 ≤ alphaQ_s32_r2 c := by
    unfold alphaQ_s32_r2
    positivity
  have hprob : ∑ c, alphaQ_s32_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![335739995,79186771988,840954976683,79186776867,335734467] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![180620571484,638758859466,180620569050,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s32_r2 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![12,4,0,4,12] ![12,4,0,4,12] ![3,1,3,40,40] jointExponent_s32_r2 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 32 => c.val 0)
        (fun c => (alphaQ_s32_r2 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s32_r2 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s32_r2, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s32_r4 (c : MME.ReleasedInterior.Split 32) : ℚ :=
  (splitWeight 1 32 4 c : ℚ) / 1000000000000

private def jointExponent_s32_r4 (c : MME.ReleasedInterior.Split 32) : ℕ :=
  [12, 5, 5, 3, 1, 3, 5, 5, 12].getD ((seed 1 32).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s32_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 32 => c.val 0)
        (fun c => (splitWeight 1 32 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 32 => (splitWeight 1 32 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 32) : 0 ≤ alphaQ_s32_r4 c := by
    unfold alphaQ_s32_r4
    positivity
  have hprob : ∑ c, alphaQ_s32_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![335756429,79190091596,840948306160,79190071874,335773941] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![180575420797,638849160158,180575419045,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s32_r4 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![12,4,0,4,12] ![12,4,0,4,12] ![3,1,3,40,40] jointExponent_s32_r4 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 32 => c.val 0)
        (fun c => (alphaQ_s32_r4 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s32_r4 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s32_r4, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s33_r3 (c : MME.ReleasedInterior.Split 33) : ℚ :=
  (splitWeight 1 33 3 c : ℚ) / 1000000000000

private def jointExponent_s33_r3 (c : MME.ReleasedInterior.Split 33) : ℕ :=
  [12, 6, 4, 1, 1, 4, 6, 12].getD ((seed 1 33).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s33_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 33 => c.val 0)
        (fun c => (splitWeight 1 33 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 33 => (splitWeight 1 33 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 33) : 0 ≤ alphaQ_s33_r3 c := by
    unfold alphaQ_s33_r3
    positivity
  have hprob : ∑ c, alphaQ_s33_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![330102971,80555873832,838228039690,80555880278,330103229] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999989571,500000010429,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s33_r4 (c : MME.ReleasedInterior.Split 33) : ℚ :=
  (splitWeight 1 33 4 c : ℚ) / 1000000000000

private def jointExponent_s33_r4 (c : MME.ReleasedInterior.Split 33) : ℕ :=
  [12, 6, 4, 1, 1, 4, 6, 12].getD ((seed 1 33).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s33_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 33 => c.val 0)
        (fun c => (splitWeight 1 33 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 33 => (splitWeight 1 33 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 33) : 0 ≤ alphaQ_s33_r4 c := by
    unfold alphaQ_s33_r4
    positivity
  have hprob : ∑ c, alphaQ_s33_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![326414523,77743389971,843860387364,77743392688,326415454] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999994019,500000005981,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s33_r4 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![12,4,0,4,12] ![12,4,0,4,12] ![1,1,40,40,40] jointExponent_s33_r4 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 33 => c.val 0)
        (fun c => (alphaQ_s33_r4 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s33_r4 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s33_r4, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s33_r5 (c : MME.ReleasedInterior.Split 33) : ℚ :=
  (splitWeight 1 33 5 c : ℚ) / 1000000000000

private def jointExponent_s33_r5 (c : MME.ReleasedInterior.Split 33) : ℕ :=
  [12, 6, 4, 1, 1, 4, 6, 12].getD ((seed 1 33).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s33_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 33 => c.val 0)
        (fun c => (splitWeight 1 33 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 33 => (splitWeight 1 33 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 33) : 0 ≤ alphaQ_s33_r5 c := by
    unfold alphaQ_s33_r5
    positivity
  have hprob : ∑ c, alphaQ_s33_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![328743195,80482030438,838378444172,80482038523,328743672] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999984507,500000015493,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s36_r1 (c : MME.ReleasedInterior.Split 36) : ℚ :=
  (splitWeight 1 36 1 c : ℚ) / 1000000000000

private def jointExponent_s36_r1 (c : MME.ReleasedInterior.Split 36) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 1 36).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s36_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 36 => c.val 0)
        (fun c => (splitWeight 1 36 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 36 => (splitWeight 1 36 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 36) : 0 ≤ alphaQ_s36_r1 c := by
    unfold alphaQ_s36_r1
    positivity
  have hprob : ∑ c, alphaQ_s36_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7318842669,492685090521,492681245786,7314821024] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499991353043,500008646957,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s36_r1 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![0,7,1,1,7] ![40,7,1,1,7] ![1,1,40,40,40] jointExponent_s36_r1 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 36 => c.val 0)
        (fun c => (alphaQ_s36_r1 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s36_r1 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s36_r1, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s36_r2 (c : MME.ReleasedInterior.Split 36) : ℚ :=
  (splitWeight 1 36 2 c : ℚ) / 1000000000000

private def jointExponent_s36_r2 (c : MME.ReleasedInterior.Split 36) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 1 36).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s36_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 36 => c.val 0)
        (fun c => (splitWeight 1 36 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 36 => (splitWeight 1 36 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 36) : 0 ≤ alphaQ_s36_r2 c := by
    unfold alphaQ_s36_r2
    positivity
  have hprob : ∑ c, alphaQ_s36_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7256956617,492743047576,492743048935,7256946872] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999990358,500000009642,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 1 36 3 c : ℚ) / 1000000000000

private def jointExponent_s36_r3 (c : MME.ReleasedInterior.Split 36) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 1 36).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s36_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 36 => c.val 0)
        (fun c => (splitWeight 1 36 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 36 => (splitWeight 1 36 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 36) : 0 ≤ alphaQ_s36_r3 c := by
    unfold alphaQ_s36_r3
    positivity
  have hprob : ∑ c, alphaQ_s36_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7354003462,492646001583,492645933366,7354061589] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000012001,499999987999,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 1 36 4 c : ℚ) / 1000000000000

private def jointExponent_s36_r4 (c : MME.ReleasedInterior.Split 36) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 1 36).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s36_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 36 => c.val 0)
        (fun c => (splitWeight 1 36 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 36 => (splitWeight 1 36 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 36) : 0 ≤ alphaQ_s36_r4 c := by
    unfold alphaQ_s36_r4
    positivity
  have hprob : ∑ c, alphaQ_s36_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7328489949,492671486827,492671515973,7328507251] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000022779,499999977221,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 1 36 5 c : ℚ) / 1000000000000

private def jointExponent_s36_r5 (c : MME.ReleasedInterior.Split 36) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 1 36).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s36_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 36 => c.val 0)
        (fun c => (splitWeight 1 36 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 36 => (splitWeight 1 36 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 36) : 0 ≤ alphaQ_s36_r5 c := by
    unfold alphaQ_s36_r5
    positivity
  have hprob : ∑ c, alphaQ_s36_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7370194268,492629803341,492629824476,7370177915] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999994257,500000005743,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s37_r0 (c : MME.ReleasedInterior.Split 37) : ℚ :=
  (splitWeight 1 37 0 c : ℚ) / 1000000000000

private def jointExponent_s37_r0 (c : MME.ReleasedInterior.Split 37) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 1 37).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s37_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 37 => c.val 0)
        (fun c => (splitWeight 1 37 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 37 => (splitWeight 1 37 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 37) : 0 ≤ alphaQ_s37_r0 c := by
    unfold alphaQ_s37_r0
    positivity
  have hprob : ∑ c, alphaQ_s37_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7313923380,492686069205,492686086859,7313920556] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000002478,499999997522,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s37_r0 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![0,7,1,1,7] ![40,7,1,1,7] ![1,1,40,40,40] jointExponent_s37_r0 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 37 => c.val 0)
        (fun c => (alphaQ_s37_r0 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s37_r0 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s37_r0, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s37_r2 (c : MME.ReleasedInterior.Split 37) : ℚ :=
  (splitWeight 1 37 2 c : ℚ) / 1000000000000

private def jointExponent_s37_r2 (c : MME.ReleasedInterior.Split 37) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 1 37).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s37_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 37 => c.val 0)
        (fun c => (splitWeight 1 37 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 37 => (splitWeight 1 37 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 37) : 0 ≤ alphaQ_s37_r2 c := by
    unfold alphaQ_s37_r2
    positivity
  have hprob : ∑ c, alphaQ_s37_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7326426605,492673588294,492673578136,7326406965] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999977599,500000022401,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 1 37 3 c : ℚ) / 1000000000000

private def jointExponent_s37_r3 (c : MME.ReleasedInterior.Split 37) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 1 37).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s37_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 37 => c.val 0)
        (fun c => (splitWeight 1 37 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 37 => (splitWeight 1 37 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 37) : 0 ≤ alphaQ_s37_r3 c := by
    unfold alphaQ_s37_r3
    positivity
  have hprob : ∑ c, alphaQ_s37_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7365533580,492634463276,492634478471,7365524673] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999999782,500000000218,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 1 37 4 c : ℚ) / 1000000000000

private def jointExponent_s37_r4 (c : MME.ReleasedInterior.Split 37) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 1 37).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s37_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 37 => c.val 0)
        (fun c => (splitWeight 1 37 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 37 => (splitWeight 1 37 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 37) : 0 ≤ alphaQ_s37_r4 c := by
    unfold alphaQ_s37_r4
    positivity
  have hprob : ∑ c, alphaQ_s37_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7254409661,492745586094,492745586286,7254417959] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000007478,499999992522,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 1 37 5 c : ℚ) / 1000000000000

private def jointExponent_s37_r5 (c : MME.ReleasedInterior.Split 37) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 1 37).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s37_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 37 => c.val 0)
        (fun c => (splitWeight 1 37 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 37 => (splitWeight 1 37 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 37) : 0 ≤ alphaQ_s37_r5 c := by
    unfold alphaQ_s37_r5
    positivity
  have hprob : ∑ c, alphaQ_s37_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7351473493,492648517418,492648603637,7351405452] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999987117,500000012883,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 1 40 0 c : ℚ) / 1000000000000

private def jointExponent_s40_r0 (c : MME.ReleasedInterior.Split 40) : ℕ :=
  [3, 1, 1, 3].getD ((seed 1 40).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s40_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 40 => c.val 0)
        (fun c => (splitWeight 1 40 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 40 => (splitWeight 1 40 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 40) : 0 ≤ alphaQ_s40_r0 c := by
    unfold alphaQ_s40_r0
    positivity
  have hprob : ∑ c, alphaQ_s40_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499982420369,500017579631,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500008987601,499991012399,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 1 40 1 c : ℚ) / 1000000000000

private def jointExponent_s40_r1 (c : MME.ReleasedInterior.Split 40) : ℕ :=
  [3, 1, 1, 3].getD ((seed 1 40).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s40_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 40 => c.val 0)
        (fun c => (splitWeight 1 40 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 40 => (splitWeight 1 40 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 40) : 0 ≤ alphaQ_s40_r1 c := by
    unfold alphaQ_s40_r1
    positivity
  have hprob : ∑ c, alphaQ_s40_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999997255,500000002745,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999998850,500000001150,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 1 40 2 c : ℚ) / 1000000000000

private def jointExponent_s40_r2 (c : MME.ReleasedInterior.Split 40) : ℕ :=
  [3, 1, 1, 3].getD ((seed 1 40).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s40_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 40 => c.val 0)
        (fun c => (splitWeight 1 40 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 40 => (splitWeight 1 40 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 40) : 0 ≤ alphaQ_s40_r2 c := by
    unfold alphaQ_s40_r2
    positivity
  have hprob : ∑ c, alphaQ_s40_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999997509,500000002491,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999998190,500000001810,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 1 40 3 c : ℚ) / 1000000000000

private def jointExponent_s40_r3 (c : MME.ReleasedInterior.Split 40) : ℕ :=
  [3, 1, 1, 3].getD ((seed 1 40).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s40_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 40 => c.val 0)
        (fun c => (splitWeight 1 40 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 40 => (splitWeight 1 40 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 40) : 0 ≤ alphaQ_s40_r3 c := by
    unfold alphaQ_s40_r3
    positivity
  have hprob : ∑ c, alphaQ_s40_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999999913,500000000087,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999999918,500000000082,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 1 40 4 c : ℚ) / 1000000000000

private def jointExponent_s40_r4 (c : MME.ReleasedInterior.Split 40) : ℕ :=
  [3, 1, 1, 3].getD ((seed 1 40).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s40_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 40 => c.val 0)
        (fun c => (splitWeight 1 40 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 40 => (splitWeight 1 40 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 40) : 0 ≤ alphaQ_s40_r4 c := by
    unfold alphaQ_s40_r4
    positivity
  have hprob : ∑ c, alphaQ_s40_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999998286,500000001714,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999997780,500000002220,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 1 40 5 c : ℚ) / 1000000000000

private def jointExponent_s40_r5 (c : MME.ReleasedInterior.Split 40) : ℕ :=
  [3, 1, 1, 3].getD ((seed 1 40).splits.idxOf (sourceShape 1 c)) 0

private theorem region_s40_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 40 => c.val 0)
        (fun c => (splitWeight 1 40 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 40 => (splitWeight 1 40 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 40) : 0 ≤ alphaQ_s40_r5 c := by
    unfold alphaQ_s40_r5
    positivity
  have hprob : ∑ c, alphaQ_s40_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999997785,500000002215,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999997326,500000002674,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
    (s : Fin 45) (r : Fin 6) (hi : (seed 1 s).boundary = [])
    (hn : 0 < (seed 1 s).region.getD r.val 0) :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split s => c.val 0)
        (fun c => (splitWeight 1 s r c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split s => (splitWeight 1 s r c : ℝ) / 1000000000000) := by
  fin_cases s
  · exact False.elim ((by decide +kernel : (seed 1 0).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 1 1).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 1 2).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 1 3).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 1 4).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 1 5).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 1 6).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 1 7).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 1 8).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 1 9).boundary ≠ []) hi)
  · fin_cases r
    · exact region_s10_r0
    · exact region_s10_r1
    · exact region_s10_r2
    · exact region_s10_r3
    · exact region_s10_r4
    · exact region_s10_r5
  · fin_cases r
    · have hz : (seed 1 11).region.getD 0 0 = 0 := by decide +kernel
      change 0 < (seed 1 11).region.getD 0 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s11_r1
    · have hz : (seed 1 11).region.getD 2 0 = 0 := by decide +kernel
      change 0 < (seed 1 11).region.getD 2 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 1 11).region.getD 3 0 = 0 := by decide +kernel
      change 0 < (seed 1 11).region.getD 3 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s11_r4
    · exact region_s11_r5
  · fin_cases r
    · have hz : (seed 1 12).region.getD 0 0 = 0 := by decide +kernel
      change 0 < (seed 1 12).region.getD 0 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s12_r1
    · have hz : (seed 1 12).region.getD 2 0 = 0 := by decide +kernel
      change 0 < (seed 1 12).region.getD 2 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 1 12).region.getD 3 0 = 0 := by decide +kernel
      change 0 < (seed 1 12).region.getD 3 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s12_r4
    · exact region_s12_r5
  · fin_cases r
    · exact region_s13_r0
    · have hz : (seed 1 13).region.getD 1 0 = 0 := by decide +kernel
      change 0 < (seed 1 13).region.getD 1 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s13_r2
    · exact region_s13_r3
    · have hz : (seed 1 13).region.getD 4 0 = 0 := by decide +kernel
      change 0 < (seed 1 13).region.getD 4 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 1 13).region.getD 5 0 = 0 := by decide +kernel
      change 0 < (seed 1 13).region.getD 5 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
  · fin_cases r
    · exact region_s14_r0
    · exact region_s14_r1
    · exact region_s14_r2
    · exact region_s14_r3
    · exact region_s14_r4
    · have hz : (seed 1 14).region.getD 5 0 = 0 := by decide +kernel
      change 0 < (seed 1 14).region.getD 5 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
  · fin_cases r
    · exact region_s15_r0
    · exact region_s15_r1
    · exact region_s15_r2
    · exact region_s15_r3
    · exact region_s15_r4
    · exact region_s15_r5
  · exact False.elim ((by decide +kernel : (seed 1 16).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 1 17).boundary ≠ []) hi)
  · fin_cases r
    · exact region_s18_r0
    · exact region_s18_r1
    · have hz : (seed 1 18).region.getD 2 0 = 0 := by decide +kernel
      change 0 < (seed 1 18).region.getD 2 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 1 18).region.getD 3 0 = 0 := by decide +kernel
      change 0 < (seed 1 18).region.getD 3 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s18_r4
    · have hz : (seed 1 18).region.getD 5 0 = 0 := by decide +kernel
      change 0 < (seed 1 18).region.getD 5 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
  · fin_cases r
    · exact region_s19_r0
    · exact region_s19_r1
    · have hz : (seed 1 19).region.getD 2 0 = 0 := by decide +kernel
      change 0 < (seed 1 19).region.getD 2 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 1 19).region.getD 3 0 = 0 := by decide +kernel
      change 0 < (seed 1 19).region.getD 3 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s19_r4
    · exact region_s19_r5
  · fin_cases r
    · have hz : (seed 1 20).region.getD 0 0 = 0 := by decide +kernel
      change 0 < (seed 1 20).region.getD 0 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 1 20).region.getD 1 0 = 0 := by decide +kernel
      change 0 < (seed 1 20).region.getD 1 0 at hn
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
    · exact region_s22_r2
    · exact region_s22_r3
    · have hz : (seed 1 22).region.getD 4 0 = 0 := by decide +kernel
      change 0 < (seed 1 22).region.getD 4 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s22_r5
  · exact False.elim ((by decide +kernel : (seed 1 23).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 1 24).boundary ≠ []) hi)
  · fin_cases r
    · exact region_s25_r0
    · exact region_s25_r1
    · have hz : (seed 1 25).region.getD 2 0 = 0 := by decide +kernel
      change 0 < (seed 1 25).region.getD 2 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 1 25).region.getD 3 0 = 0 := by decide +kernel
      change 0 < (seed 1 25).region.getD 3 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s25_r4
    · have hz : (seed 1 25).region.getD 5 0 = 0 := by decide +kernel
      change 0 < (seed 1 25).region.getD 5 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
  · fin_cases r
    · exact region_s26_r0
    · exact region_s26_r1
    · exact region_s26_r2
    · exact region_s26_r3
    · have hz : (seed 1 26).region.getD 4 0 = 0 := by decide +kernel
      change 0 < (seed 1 26).region.getD 4 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 1 26).region.getD 5 0 = 0 := by decide +kernel
      change 0 < (seed 1 26).region.getD 5 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
  · fin_cases r
    · exact region_s27_r0
    · exact region_s27_r1
    · have hz : (seed 1 27).region.getD 2 0 = 0 := by decide +kernel
      change 0 < (seed 1 27).region.getD 2 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 1 27).region.getD 3 0 = 0 := by decide +kernel
      change 0 < (seed 1 27).region.getD 3 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s27_r4
    · exact region_s27_r5
  · fin_cases r
    · exact region_s28_r0
    · exact region_s28_r1
    · exact region_s28_r2
    · have hz : (seed 1 28).region.getD 3 0 = 0 := by decide +kernel
      change 0 < (seed 1 28).region.getD 3 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 1 28).region.getD 4 0 = 0 := by decide +kernel
      change 0 < (seed 1 28).region.getD 4 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 1 28).region.getD 5 0 = 0 := by decide +kernel
      change 0 < (seed 1 28).region.getD 5 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
  · exact False.elim ((by decide +kernel : (seed 1 29).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 1 30).boundary ≠ []) hi)
  · fin_cases r
    · have hz : (seed 1 31).region.getD 0 0 = 0 := by decide +kernel
      change 0 < (seed 1 31).region.getD 0 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 1 31).region.getD 1 0 = 0 := by decide +kernel
      change 0 < (seed 1 31).region.getD 1 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s31_r2
    · exact region_s31_r3
    · have hz : (seed 1 31).region.getD 4 0 = 0 := by decide +kernel
      change 0 < (seed 1 31).region.getD 4 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s31_r5
  · fin_cases r
    · exact region_s32_r0
    · exact region_s32_r1
    · exact region_s32_r2
    · have hz : (seed 1 32).region.getD 3 0 = 0 := by decide +kernel
      change 0 < (seed 1 32).region.getD 3 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s32_r4
    · have hz : (seed 1 32).region.getD 5 0 = 0 := by decide +kernel
      change 0 < (seed 1 32).region.getD 5 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
  · fin_cases r
    · have hz : (seed 1 33).region.getD 0 0 = 0 := by decide +kernel
      change 0 < (seed 1 33).region.getD 0 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 1 33).region.getD 1 0 = 0 := by decide +kernel
      change 0 < (seed 1 33).region.getD 1 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 1 33).region.getD 2 0 = 0 := by decide +kernel
      change 0 < (seed 1 33).region.getD 2 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s33_r3
    · exact region_s33_r4
    · exact region_s33_r5
  · exact False.elim ((by decide +kernel : (seed 1 34).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 1 35).boundary ≠ []) hi)
  · fin_cases r
    · have hz : (seed 1 36).region.getD 0 0 = 0 := by decide +kernel
      change 0 < (seed 1 36).region.getD 0 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s36_r1
    · exact region_s36_r2
    · exact region_s36_r3
    · exact region_s36_r4
    · exact region_s36_r5
  · fin_cases r
    · exact region_s37_r0
    · have hz : (seed 1 37).region.getD 1 0 = 0 := by decide +kernel
      change 0 < (seed 1 37).region.getD 1 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s37_r2
    · exact region_s37_r3
    · exact region_s37_r4
    · exact region_s37_r5
  · exact False.elim ((by decide +kernel : (seed 1 38).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 1 39).boundary ≠ []) hi)
  · fin_cases r
    · exact region_s40_r0
    · exact region_s40_r1
    · exact region_s40_r2
    · exact region_s40_r3
    · exact region_s40_r4
    · exact region_s40_r5
  · exact False.elim ((by decide +kernel : (seed 1 41).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 1 42).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 1 43).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 1 44).boundary ≠ []) hi)


#print axioms solution
