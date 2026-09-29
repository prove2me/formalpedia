-- Prove2me | solution 1 for mme_released_interior_owner5_region_coarse_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T07:19:14.443493+00:00
-- url     : https://prove2.me/submissions/b8430eeb-4c0b-4de3-a4e2-fdd3964b666f

import Theorems.Thm_mme_rational_coarse_penalty_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.RecursiveThinSplit MME.ReleasedInterior

private def alphaQ_s10_r0 (c : MME.ReleasedInterior.Split 10) : ℚ :=
  (splitWeight 5 10 0 c : ℚ) / 1000000000000

private def jointExponent_s10_r0 (c : MME.ReleasedInterior.Split 10) : ℕ :=
  [3, 1, 1, 3].getD ((seed 5 10).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s10_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 10 => c.val 0)
        (fun c => (splitWeight 5 10 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 10 => (splitWeight 5 10 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 10) : 0 ≤ alphaQ_s10_r0 c := by
    unfold alphaQ_s10_r0
    positivity
  have hprob : ∑ c, alphaQ_s10_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500449228292,499550771708,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499464662516,500535337484,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 10 1 c : ℚ) / 1000000000000

private def jointExponent_s10_r1 (c : MME.ReleasedInterior.Split 10) : ℕ :=
  [3, 1, 1, 3].getD ((seed 5 10).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s10_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 10 => c.val 0)
        (fun c => (splitWeight 5 10 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 10 => (splitWeight 5 10 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 10) : 0 ≤ alphaQ_s10_r1 c := by
    unfold alphaQ_s10_r1
    positivity
  have hprob : ∑ c, alphaQ_s10_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499642738602,500357261398,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500341413217,499658586783,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 10 2 c : ℚ) / 1000000000000

private def jointExponent_s10_r2 (c : MME.ReleasedInterior.Split 10) : ℕ :=
  [3, 1, 1, 3].getD ((seed 5 10).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s10_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 10 => c.val 0)
        (fun c => (splitWeight 5 10 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 10 => (splitWeight 5 10 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 10) : 0 ≤ alphaQ_s10_r2 c := by
    unfold alphaQ_s10_r2
    positivity
  have hprob : ∑ c, alphaQ_s10_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500141377474,499858622526,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499728948890,500271051110,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 10 3 c : ℚ) / 1000000000000

private def jointExponent_s10_r3 (c : MME.ReleasedInterior.Split 10) : ℕ :=
  [3, 1, 1, 3].getD ((seed 5 10).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s10_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 10 => c.val 0)
        (fun c => (splitWeight 5 10 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 10 => (splitWeight 5 10 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 10) : 0 ≤ alphaQ_s10_r3 c := by
    unfold alphaQ_s10_r3
    positivity
  have hprob : ∑ c, alphaQ_s10_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499997277671,500002722329,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499997276649,500002723351,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 10 4 c : ℚ) / 1000000000000

private def jointExponent_s10_r4 (c : MME.ReleasedInterior.Split 10) : ℕ :=
  [3, 1, 1, 3].getD ((seed 5 10).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s10_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 10 => c.val 0)
        (fun c => (splitWeight 5 10 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 10 => (splitWeight 5 10 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 10) : 0 ≤ alphaQ_s10_r4 c := by
    unfold alphaQ_s10_r4
    positivity
  have hprob : ∑ c, alphaQ_s10_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499730651980,500269348020,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500145025381,499854974619,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 10 5 c : ℚ) / 1000000000000

private def jointExponent_s10_r5 (c : MME.ReleasedInterior.Split 10) : ℕ :=
  [3, 1, 1, 3].getD ((seed 5 10).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s10_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 10 => c.val 0)
        (fun c => (splitWeight 5 10 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 10 => (splitWeight 5 10 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 10) : 0 ≤ alphaQ_s10_r5 c := by
    unfold alphaQ_s10_r5
    positivity
  have hprob : ∑ c, alphaQ_s10_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499997225843,500002774157,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499997226936,500002773064,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s11_r2 (c : MME.ReleasedInterior.Split 11) : ℚ :=
  (splitWeight 5 11 2 c : ℚ) / 1000000000000

private def jointExponent_s11_r2 (c : MME.ReleasedInterior.Split 11) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 5 11).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s11_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 11 => c.val 0)
        (fun c => (splitWeight 5 11 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 11 => (splitWeight 5 11 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 11) : 0 ≤ alphaQ_s11_r2 c := by
    unfold alphaQ_s11_r2
    positivity
  have hprob : ∑ c, alphaQ_s11_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000115904,499999884096,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,6633855130,493366230339,493365841706,6634072825] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 11 3 c : ℚ) / 1000000000000

private def jointExponent_s11_r3 (c : MME.ReleasedInterior.Split 11) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 5 11).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s11_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 11 => c.val 0)
        (fun c => (splitWeight 5 11 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 11 => (splitWeight 5 11 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 11) : 0 ≤ alphaQ_s11_r3 c := by
    unfold alphaQ_s11_r3
    positivity
  have hprob : ∑ c, alphaQ_s11_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000077617,499999922383,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,6611990497,493388099039,493387822293,6612088171] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s11_r5 (c : MME.ReleasedInterior.Split 11) : ℚ :=
  (splitWeight 5 11 5 c : ℚ) / 1000000000000

private def jointExponent_s11_r5 (c : MME.ReleasedInterior.Split 11) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 5 11).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s11_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 11 => c.val 0)
        (fun c => (splitWeight 5 11 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 11 => (splitWeight 5 11 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 11) : 0 ≤ alphaQ_s11_r5 c := by
    unfold alphaQ_s11_r5
    positivity
  have hprob : ∑ c, alphaQ_s11_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000675909,499999324091,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,6586945397,493414111462,493407780184,6591162957] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s12_r2 (c : MME.ReleasedInterior.Split 12) : ℚ :=
  (splitWeight 5 12 2 c : ℚ) / 1000000000000

private def jointExponent_s12_r2 (c : MME.ReleasedInterior.Split 12) : ℕ :=
  [12, 4, 6, 1, 1, 6, 4, 12].getD ((seed 5 12).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s12_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 12 => c.val 0)
        (fun c => (splitWeight 5 12 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 12 => (splitWeight 5 12 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 12) : 0 ≤ alphaQ_s12_r2 c := by
    unfold alphaQ_s12_r2
    positivity
  have hprob : ∑ c, alphaQ_s12_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000003411,499999996589,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![325717274,70609379088,858129813665,70609373140,325716833] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 12 3 c : ℚ) / 1000000000000

private def jointExponent_s12_r3 (c : MME.ReleasedInterior.Split 12) : ℕ :=
  [12, 4, 6, 1, 1, 6, 4, 12].getD ((seed 5 12).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s12_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 12 => c.val 0)
        (fun c => (splitWeight 5 12 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 12 => (splitWeight 5 12 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 12) : 0 ≤ alphaQ_s12_r3 c := by
    unfold alphaQ_s12_r3
    positivity
  have hprob : ∑ c, alphaQ_s12_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000021755,499999978245,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![323436205,73603520463,852146101851,73603505302,323436179] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s12_r5 (c : MME.ReleasedInterior.Split 12) : ℚ :=
  (splitWeight 5 12 5 c : ℚ) / 1000000000000

private def jointExponent_s12_r5 (c : MME.ReleasedInterior.Split 12) : ℕ :=
  [12, 4, 6, 1, 1, 6, 4, 12].getD ((seed 5 12).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s12_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 12 => c.val 0)
        (fun c => (splitWeight 5 12 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 12 => (splitWeight 5 12 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 12) : 0 ≤ alphaQ_s12_r5 c := by
    unfold alphaQ_s12_r5
    positivity
  have hprob : ∑ c, alphaQ_s12_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000027713,499999972287,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![326380081,73580761232,852185737754,73580739166,326381767] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 13 0 c : ℚ) / 1000000000000

private def jointExponent_s13_r0 (c : MME.ReleasedInterior.Split 13) : ℕ :=
  [6, 12, 1, 4, 4, 1, 12, 6].getD ((seed 5 13).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s13_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 13 => c.val 0)
        (fun c => (splitWeight 5 13 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 13 => (splitWeight 5 13 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 13) : 0 ≤ alphaQ_s13_r0 c := by
    unfold alphaQ_s13_r0
    positivity
  have hprob : ∑ c, alphaQ_s13_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000004199,499999995801,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![323999607,74867011642,849617977586,74867001883,324009282] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s13_r1 (c : MME.ReleasedInterior.Split 13) : ℚ :=
  (splitWeight 5 13 1 c : ℚ) / 1000000000000

private def jointExponent_s13_r1 (c : MME.ReleasedInterior.Split 13) : ℕ :=
  [6, 12, 1, 4, 4, 1, 12, 6].getD ((seed 5 13).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s13_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 13 => c.val 0)
        (fun c => (splitWeight 5 13 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 13 => (splitWeight 5 13 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 13) : 0 ≤ alphaQ_s13_r1 c := by
    unfold alphaQ_s13_r1
    positivity
  have hprob : ∑ c, alphaQ_s13_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999987736,500000012264,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![325644323,77664627684,844019450043,77664628082,325649868] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 13 4 c : ℚ) / 1000000000000

private def jointExponent_s13_r4 (c : MME.ReleasedInterior.Split 13) : ℕ :=
  [6, 12, 1, 4, 4, 1, 12, 6].getD ((seed 5 13).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s13_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 13 => c.val 0)
        (fun c => (splitWeight 5 13 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 13 => (splitWeight 5 13 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 13) : 0 ≤ alphaQ_s13_r4 c := by
    unfold alphaQ_s13_r4
    positivity
  have hprob : ∑ c, alphaQ_s13_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000003010,499999996990,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![327224329,77708102638,843929351708,77708101845,327219480] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s14_r0 (c : MME.ReleasedInterior.Split 14) : ℚ :=
  (splitWeight 5 14 0 c : ℚ) / 1000000000000

private def jointExponent_s14_r0 (c : MME.ReleasedInterior.Split 14) : ℕ :=
  [3, 7, 2, 2, 7, 3].getD ((seed 5 14).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s14_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 14 => c.val 0)
        (fun c => (splitWeight 5 14 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 14 => (splitWeight 5 14 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 14) : 0 ≤ alphaQ_s14_r0 c := by
    unfold alphaQ_s14_r0
    positivity
  have hprob : ∑ c, alphaQ_s14_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000008754,499999991246,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,7036877699,492963259093,492962819447,7037043761] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 14 1 c : ℚ) / 1000000000000

private def jointExponent_s14_r1 (c : MME.ReleasedInterior.Split 14) : ℕ :=
  [3, 7, 2, 2, 7, 3].getD ((seed 5 14).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s14_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 14 => c.val 0)
        (fun c => (splitWeight 5 14 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 14 => (splitWeight 5 14 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 14) : 0 ≤ alphaQ_s14_r1 c := by
    unfold alphaQ_s14_r1
    positivity
  have hprob : ∑ c, alphaQ_s14_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499998894191,500001105809,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,7075982272,492923475235,492929119335,7071423158] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s14_r3 (c : MME.ReleasedInterior.Split 14) : ℚ :=
  (splitWeight 5 14 3 c : ℚ) / 1000000000000

private def jointExponent_s14_r3 (c : MME.ReleasedInterior.Split 14) : ℕ :=
  [3, 7, 2, 2, 7, 3].getD ((seed 5 14).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s14_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 14 => c.val 0)
        (fun c => (splitWeight 5 14 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 14 => (splitWeight 5 14 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 14) : 0 ≤ alphaQ_s14_r3 c := by
    unfold alphaQ_s14_r3
    positivity
  have hprob : ∑ c, alphaQ_s14_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499994283359,500005716641,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,7158344159,492844359979,492841305448,7155990414] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 14 4 c : ℚ) / 1000000000000

private def jointExponent_s14_r4 (c : MME.ReleasedInterior.Split 14) : ℕ :=
  [3, 7, 2, 2, 7, 3].getD ((seed 5 14).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s14_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 14 => c.val 0)
        (fun c => (splitWeight 5 14 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 14 => (splitWeight 5 14 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 14) : 0 ≤ alphaQ_s14_r4 c := by
    unfold alphaQ_s14_r4
    positivity
  have hprob : ∑ c, alphaQ_s14_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999991557,500000008443,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,7073016045,492927063335,492926941414,7072979206] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 14 5 c : ℚ) / 1000000000000

private def jointExponent_s14_r5 (c : MME.ReleasedInterior.Split 14) : ℕ :=
  [3, 7, 2, 2, 7, 3].getD ((seed 5 14).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s14_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 14 => c.val 0)
        (fun c => (splitWeight 5 14 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 14 => (splitWeight 5 14 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 14) : 0 ≤ alphaQ_s14_r5 c := by
    unfold alphaQ_s14_r5
    positivity
  have hprob : ∑ c, alphaQ_s14_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999806496,500000193504,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,7160773985,492839447335,492839396645,7160382035] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 15 0 c : ℚ) / 1000000000000

private def jointExponent_s15_r0 (c : MME.ReleasedInterior.Split 15) : ℕ :=
  [1, 3, 3, 1].getD ((seed 5 15).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s15_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 15 => c.val 0)
        (fun c => (splitWeight 5 15 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 15 => (splitWeight 5 15 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 15) : 0 ≤ alphaQ_s15_r0 c := by
    unfold alphaQ_s15_r0
    positivity
  have hprob : ∑ c, alphaQ_s15_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500202655235,499797344765,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500168466990,499831533010,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 15 1 c : ℚ) / 1000000000000

private def jointExponent_s15_r1 (c : MME.ReleasedInterior.Split 15) : ℕ :=
  [1, 3, 3, 1].getD ((seed 5 15).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s15_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 15 => c.val 0)
        (fun c => (splitWeight 5 15 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 15 => (splitWeight 5 15 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 15) : 0 ≤ alphaQ_s15_r1 c := by
    unfold alphaQ_s15_r1
    positivity
  have hprob : ∑ c, alphaQ_s15_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500158565572,499841434428,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500131679572,499868320428,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 15 2 c : ℚ) / 1000000000000

private def jointExponent_s15_r2 (c : MME.ReleasedInterior.Split 15) : ℕ :=
  [1, 3, 3, 1].getD ((seed 5 15).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s15_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 15 => c.val 0)
        (fun c => (splitWeight 5 15 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 15 => (splitWeight 5 15 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 15) : 0 ≤ alphaQ_s15_r2 c := by
    unfold alphaQ_s15_r2
    positivity
  have hprob : ∑ c, alphaQ_s15_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500212692104,499787307896,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500175823905,499824176095,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 15 3 c : ℚ) / 1000000000000

private def jointExponent_s15_r3 (c : MME.ReleasedInterior.Split 15) : ℕ :=
  [1, 3, 3, 1].getD ((seed 5 15).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s15_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 15 => c.val 0)
        (fun c => (splitWeight 5 15 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 15 => (splitWeight 5 15 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 15) : 0 ≤ alphaQ_s15_r3 c := by
    unfold alphaQ_s15_r3
    positivity
  have hprob : ∑ c, alphaQ_s15_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500205815835,499794184165,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500168233592,499831766408,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 15 4 c : ℚ) / 1000000000000

private def jointExponent_s15_r4 (c : MME.ReleasedInterior.Split 15) : ℕ :=
  [1, 3, 3, 1].getD ((seed 5 15).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s15_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 15 => c.val 0)
        (fun c => (splitWeight 5 15 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 15 => (splitWeight 5 15 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 15) : 0 ≤ alphaQ_s15_r4 c := by
    unfold alphaQ_s15_r4
    positivity
  have hprob : ∑ c, alphaQ_s15_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500158809456,499841190544,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500131637741,499868362259,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 15 5 c : ℚ) / 1000000000000

private def jointExponent_s15_r5 (c : MME.ReleasedInterior.Split 15) : ℕ :=
  [1, 3, 3, 1].getD ((seed 5 15).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s15_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 15 => c.val 0)
        (fun c => (splitWeight 5 15 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 15 => (splitWeight 5 15 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 15) : 0 ≤ alphaQ_s15_r5 c := by
    unfold alphaQ_s15_r5
    positivity
  have hprob : ∑ c, alphaQ_s15_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500181167601,499818832399,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500149358308,499850641692,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s18_r3 (c : MME.ReleasedInterior.Split 18) : ℚ :=
  (splitWeight 5 18 3 c : ℚ) / 1000000000000

private def jointExponent_s18_r3 (c : MME.ReleasedInterior.Split 18) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 5 18).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s18_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 18 => c.val 0)
        (fun c => (splitWeight 5 18 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 18 => (splitWeight 5 18 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 18) : 0 ≤ alphaQ_s18_r3 c := by
    unfold alphaQ_s18_r3
    positivity
  have hprob : ∑ c, alphaQ_s18_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000076606,499999923394,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,6589683069,493410428829,493410059106,6589828996] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s18_r3 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![3,1,3,0,0] ![1,1,40,40,40] ![40,7,1,1,7] jointExponent_s18_r3 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 18 => c.val 0)
        (fun c => (alphaQ_s18_r3 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s18_r3 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s18_r3, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s18_r4 (c : MME.ReleasedInterior.Split 18) : ℚ :=
  (splitWeight 5 18 4 c : ℚ) / 1000000000000

private def jointExponent_s18_r4 (c : MME.ReleasedInterior.Split 18) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 5 18).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s18_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 18 => c.val 0)
        (fun c => (splitWeight 5 18 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 18 => (splitWeight 5 18 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 18) : 0 ≤ alphaQ_s18_r4 c := by
    unfold alphaQ_s18_r4
    positivity
  have hprob : ∑ c, alphaQ_s18_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000098490,499999901510,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,6634148127,493365913684,493365668457,6634269732] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s18_r5 (c : MME.ReleasedInterior.Split 18) : ℚ :=
  (splitWeight 5 18 5 c : ℚ) / 1000000000000

private def jointExponent_s18_r5 (c : MME.ReleasedInterior.Split 18) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 5 18).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s18_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 18 => c.val 0)
        (fun c => (splitWeight 5 18 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 18 => (splitWeight 5 18 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 18) : 0 ≤ alphaQ_s18_r5 c := by
    unfold alphaQ_s18_r5
    positivity
  have hprob : ∑ c, alphaQ_s18_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000081943,499999918057,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,6612802191,493387301415,493386949740,6612946654] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s18_r5 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![3,1,3,0,0] ![1,1,40,40,40] ![40,7,1,1,7] jointExponent_s18_r5 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 18 => c.val 0)
        (fun c => (alphaQ_s18_r5 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s18_r5 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s18_r5, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s19_r2 (c : MME.ReleasedInterior.Split 19) : ℚ :=
  (splitWeight 5 19 2 c : ℚ) / 1000000000000

private def jointExponent_s19_r2 (c : MME.ReleasedInterior.Split 19) : ℕ :=
  [12, 5, 5, 3, 1, 3, 5, 5, 12].getD ((seed 5 19).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s19_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 19 => c.val 0)
        (fun c => (splitWeight 5 19 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 19 => (splitWeight 5 19 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 19) : 0 ≤ alphaQ_s19_r2 c := by
    unfold alphaQ_s19_r2
    positivity
  have hprob : ∑ c, alphaQ_s19_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![180521181686,638957642231,180521176083,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![318973485,71771680558,855818698630,71771655152,318992175] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 19 3 c : ℚ) / 1000000000000

private def jointExponent_s19_r3 (c : MME.ReleasedInterior.Split 19) : ℕ :=
  [12, 5, 5, 3, 1, 3, 5, 5, 12].getD ((seed 5 19).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s19_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 19 => c.val 0)
        (fun c => (splitWeight 5 19 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 19 => (splitWeight 5 19 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 19) : 0 ≤ alphaQ_s19_r3 c := by
    unfold alphaQ_s19_r3
    positivity
  have hprob : ∑ c, alphaQ_s19_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![183348547567,633302910724,183348541709,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![320772525,72977374493,853403705997,72977362108,320784877] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s19_r4 (c : MME.ReleasedInterior.Split 19) : ℚ :=
  (splitWeight 5 19 4 c : ℚ) / 1000000000000

private def jointExponent_s19_r4 (c : MME.ReleasedInterior.Split 19) : ℕ :=
  [12, 5, 5, 3, 1, 3, 5, 5, 12].getD ((seed 5 19).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s19_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 19 => c.val 0)
        (fun c => (splitWeight 5 19 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 19 => (splitWeight 5 19 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 19) : 0 ≤ alphaQ_s19_r4 c := by
    unfold alphaQ_s19_r4
    positivity
  have hprob : ∑ c, alphaQ_s19_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![180441408889,639117185941,180441405170,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![318813034,71761393336,855839603277,71761342861,318847492] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s19_r4 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![3,1,3,0,0] ![3,1,3,40,40] ![12,4,0,4,12] jointExponent_s19_r4 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 19 => c.val 0)
        (fun c => (alphaQ_s19_r4 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s19_r4 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s19_r4, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s19_r5 (c : MME.ReleasedInterior.Split 19) : ℚ :=
  (splitWeight 5 19 5 c : ℚ) / 1000000000000

private def jointExponent_s19_r5 (c : MME.ReleasedInterior.Split 19) : ℕ :=
  [12, 5, 5, 3, 1, 3, 5, 5, 12].getD ((seed 5 19).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s19_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 19 => c.val 0)
        (fun c => (splitWeight 5 19 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 19 => (splitWeight 5 19 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 19) : 0 ≤ alphaQ_s19_r5 c := by
    unfold alphaQ_s19_r5
    positivity
  have hprob : ∑ c, alphaQ_s19_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![183323233202,633353567390,183323199408,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![319615414,72975775054,853409224233,72975697447,319687852] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s19_r5 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![3,1,3,0,0] ![3,1,3,40,40] ![12,4,0,4,12] jointExponent_s19_r5 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 19 => c.val 0)
        (fun c => (alphaQ_s19_r5 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s19_r5 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s19_r5, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s20_r0 (c : MME.ReleasedInterior.Split 20) : ℚ :=
  (splitWeight 5 20 0 c : ℚ) / 1000000000000

private def jointExponent_s20_r0 (c : MME.ReleasedInterior.Split 20) : ℕ :=
  [7, 9, 3, 2, 7, 7, 2, 3, 9, 7].getD ((seed 5 20).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s20_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 20 => c.val 0)
        (fun c => (splitWeight 5 20 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 20 => (splitWeight 5 20 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 20) : 0 ≤ alphaQ_s20_r0 c := by
    unfold alphaQ_s20_r0
    positivity
  have hprob : ∑ c, alphaQ_s20_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![13042869410,486957118601,486957061119,13042950870,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![12233860822,487766154350,487766198770,12233786058,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s20_r0 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![3,1,3,0,0] ![6,1,1,6,40] ![6,1,1,6,40] jointExponent_s20_r0 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 20 => c.val 0)
        (fun c => (alphaQ_s20_r0 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s20_r0 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s20_r0, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s20_r1 (c : MME.ReleasedInterior.Split 20) : ℚ :=
  (splitWeight 5 20 1 c : ℚ) / 1000000000000

private def jointExponent_s20_r1 (c : MME.ReleasedInterior.Split 20) : ℕ :=
  [7, 9, 3, 2, 6, 6, 2, 3, 9, 7].getD ((seed 5 20).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s20_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 20 => c.val 0)
        (fun c => (splitWeight 5 20 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 20 => (splitWeight 5 20 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 20) : 0 ≤ alphaQ_s20_r1 c := by
    unfold alphaQ_s20_r1
    positivity
  have hprob : ∑ c, alphaQ_s20_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![13655806618,486344175134,486344103492,13655914756,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![12671172807,487328852699,487328907240,12671067254,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s20_r1 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![3,1,3,0,0] ![6,1,1,6,40] ![6,1,1,6,40] jointExponent_s20_r1 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 20 => c.val 0)
        (fun c => (alphaQ_s20_r1 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s20_r1 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s20_r1, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s20_r2 (c : MME.ReleasedInterior.Split 20) : ℚ :=
  (splitWeight 5 20 2 c : ℚ) / 1000000000000

private def jointExponent_s20_r2 (c : MME.ReleasedInterior.Split 20) : ℕ :=
  [7, 9, 3, 2, 7, 7, 2, 3, 9, 7].getD ((seed 5 20).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s20_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 20 => c.val 0)
        (fun c => (splitWeight 5 20 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 20 => (splitWeight 5 20 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 20) : 0 ≤ alphaQ_s20_r2 c := by
    unfold alphaQ_s20_r2
    positivity
  have hprob : ∑ c, alphaQ_s20_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![12288101439,487711899508,487711913337,12288085716,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![12956744613,487043255263,487043237910,12956762214,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 20 3 c : ℚ) / 1000000000000

private def jointExponent_s20_r3 (c : MME.ReleasedInterior.Split 20) : ℕ :=
  [6, 9, 3, 2, 7, 7, 2, 3, 9, 6].getD ((seed 5 20).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s20_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 20 => c.val 0)
        (fun c => (splitWeight 5 20 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 20 => (splitWeight 5 20 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 20) : 0 ≤ alphaQ_s20_r3 c := by
    unfold alphaQ_s20_r3
    positivity
  have hprob : ∑ c, alphaQ_s20_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![12737710500,487262287289,487262286329,12737715882,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![13574227563,486425774876,486425775186,13574222375,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s21_r0 (c : MME.ReleasedInterior.Split 21) : ℚ :=
  (splitWeight 5 21 0 c : ℚ) / 1000000000000

private def jointExponent_s21_r0 (c : MME.ReleasedInterior.Split 21) : ℕ :=
  [3, 5, 12, 5, 1, 5, 12, 5, 3].getD ((seed 5 21).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s21_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 21 => c.val 0)
        (fun c => (splitWeight 5 21 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 21 => (splitWeight 5 21 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 21) : 0 ≤ alphaQ_s21_r0 c := by
    unfold alphaQ_s21_r0
    positivity
  have hprob : ∑ c, alphaQ_s21_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![328805138,76187451674,846967525401,76187392641,328825146] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![180590395735,638819108046,180590496219,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s21_r0 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![3,1,3,0,0] ![12,4,0,4,12] ![3,1,3,40,40] jointExponent_s21_r0 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 21 => c.val 0)
        (fun c => (alphaQ_s21_r0 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s21_r0 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s21_r0, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s21_r1 (c : MME.ReleasedInterior.Split 21) : ℚ :=
  (splitWeight 5 21 1 c : ℚ) / 1000000000000

private def jointExponent_s21_r1 (c : MME.ReleasedInterior.Split 21) : ℕ :=
  [3, 5, 12, 5, 1, 5, 12, 5, 3].getD ((seed 5 21).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s21_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 21 => c.val 0)
        (fun c => (splitWeight 5 21 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 21 => (splitWeight 5 21 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 21) : 0 ≤ alphaQ_s21_r1 c := by
    unfold alphaQ_s21_r1
    positivity
  have hprob : ∑ c, alphaQ_s21_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![333657778,77546915154,844238890703,77546817328,333719037] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![183441113114,633117693740,183441193146,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s21_r1 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![3,1,3,0,0] ![12,4,0,4,12] ![3,1,3,40,40] jointExponent_s21_r1 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 21 => c.val 0)
        (fun c => (alphaQ_s21_r1 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s21_r1 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s21_r1, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s21_r2 (c : MME.ReleasedInterior.Split 21) : ℚ :=
  (splitWeight 5 21 2 c : ℚ) / 1000000000000

private def jointExponent_s21_r2 (c : MME.ReleasedInterior.Split 21) : ℕ :=
  [3, 5, 12, 5, 1, 5, 12, 5, 3].getD ((seed 5 21).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s21_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 21 => c.val 0)
        (fun c => (splitWeight 5 21 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 21 => (splitWeight 5 21 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 21) : 0 ≤ alphaQ_s21_r2 c := by
    unfold alphaQ_s21_r2
    positivity
  have hprob : ∑ c, alphaQ_s21_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![328370849,76797382852,845748521033,76797408091,328317175] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![181699232562,636601402689,181699364749,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 21 3 c : ℚ) / 1000000000000

private def jointExponent_s21_r3 (c : MME.ReleasedInterior.Split 21) : ℕ :=
  [3, 5, 12, 5, 1, 5, 12, 5, 3].getD ((seed 5 21).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s21_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 21 => c.val 0)
        (fun c => (splitWeight 5 21 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 21 => (splitWeight 5 21 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 21) : 0 ≤ alphaQ_s21_r3 c := by
    unfold alphaQ_s21_r3
    positivity
  have hprob : ∑ c, alphaQ_s21_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![181625926874,636748199655,181625873471,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![328338065,76799683659,845743989272,76799689292,328299712] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s21_r3 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![3,1,3,0,0] ![3,1,3,40,40] ![12,4,0,4,12] jointExponent_s21_r3 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 21 => c.val 0)
        (fun c => (alphaQ_s21_r3 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s21_r3 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s21_r3, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s21_r4 (c : MME.ReleasedInterior.Split 21) : ℚ :=
  (splitWeight 5 21 4 c : ℚ) / 1000000000000

private def jointExponent_s21_r4 (c : MME.ReleasedInterior.Split 21) : ℕ :=
  [3, 5, 12, 5, 1, 5, 12, 5, 3].getD ((seed 5 21).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s21_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 21 => c.val 0)
        (fun c => (splitWeight 5 21 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 21 => (splitWeight 5 21 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 21) : 0 ≤ alphaQ_s21_r4 c := by
    unfold alphaQ_s21_r4
    positivity
  have hprob : ∑ c, alphaQ_s21_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![183365429796,633269248878,183365321326,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![333626390,77541157975,844250465821,77541057730,333692084] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 21 5 c : ℚ) / 1000000000000

private def jointExponent_s21_r5 (c : MME.ReleasedInterior.Split 21) : ℕ :=
  [3, 5, 12, 5, 1, 5, 12, 5, 3].getD ((seed 5 21).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s21_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 21 => c.val 0)
        (fun c => (splitWeight 5 21 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 21 => (splitWeight 5 21 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 21) : 0 ≤ alphaQ_s21_r5 c := by
    unfold alphaQ_s21_r5
    positivity
  have hprob : ∑ c, alphaQ_s21_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![180507030978,638986014711,180506954311,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![328711044,76186158770,846970302207,76186099374,328728605] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s21_r5 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![3,1,3,0,0] ![3,1,3,40,40] ![12,4,0,4,12] jointExponent_s21_r5 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 21 => c.val 0)
        (fun c => (alphaQ_s21_r5 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s21_r5 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s21_r5, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s22_r0 (c : MME.ReleasedInterior.Split 22) : ℚ :=
  (splitWeight 5 22 0 c : ℚ) / 1000000000000

private def jointExponent_s22_r0 (c : MME.ReleasedInterior.Split 22) : ℕ :=
  [3, 2, 7, 7, 2, 3].getD ((seed 5 22).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s22_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 22 => c.val 0)
        (fun c => (splitWeight 5 22 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 22 => (splitWeight 5 22 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 22) : 0 ≤ alphaQ_s22_r0 c := by
    unfold alphaQ_s22_r0
    positivity
  have hprob : ∑ c, alphaQ_s22_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7159510567,492840671422,492840200465,7159617546] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999944112,500000055888,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 22 1 c : ℚ) / 1000000000000

private def jointExponent_s22_r1 (c : MME.ReleasedInterior.Split 22) : ℕ :=
  [3, 2, 7, 7, 2, 3].getD ((seed 5 22).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s22_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 22 => c.val 0)
        (fun c => (splitWeight 5 22 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 22 => (splitWeight 5 22 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 22) : 0 ≤ alphaQ_s22_r1 c := by
    unfold alphaQ_s22_r1
    positivity
  have hprob : ∑ c, alphaQ_s22_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7073668321,492926337538,492926383840,7073610301] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999944629,500000055371,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 22 2 c : ℚ) / 1000000000000

private def jointExponent_s22_r2 (c : MME.ReleasedInterior.Split 22) : ℕ :=
  [3, 2, 7, 7, 2, 3].getD ((seed 5 22).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s22_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 22 => c.val 0)
        (fun c => (splitWeight 5 22 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 22 => (splitWeight 5 22 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 22) : 0 ≤ alphaQ_s22_r2 c := by
    unfold alphaQ_s22_r2
    positivity
  have hprob : ∑ c, alphaQ_s22_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7155307698,492844889393,492844398919,7155403990] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999938954,500000061046,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s22_r4 (c : MME.ReleasedInterior.Split 22) : ℚ :=
  (splitWeight 5 22 4 c : ℚ) / 1000000000000

private def jointExponent_s22_r4 (c : MME.ReleasedInterior.Split 22) : ℕ :=
  [3, 2, 7, 7, 2, 3].getD ((seed 5 22).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s22_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 22 => c.val 0)
        (fun c => (splitWeight 5 22 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 22 => (splitWeight 5 22 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 22) : 0 ≤ alphaQ_s22_r4 c := by
    unfold alphaQ_s22_r4
    positivity
  have hprob : ∑ c, alphaQ_s22_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7073939094,492926096604,492926095001,7073869301] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999934415,500000065585,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 22 5 c : ℚ) / 1000000000000

private def jointExponent_s22_r5 (c : MME.ReleasedInterior.Split 22) : ℕ :=
  [3, 2, 7, 7, 2, 3].getD ((seed 5 22).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s22_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 22 => c.val 0)
        (fun c => (splitWeight 5 22 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 22 => (splitWeight 5 22 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 22) : 0 ≤ alphaQ_s22_r5 c := by
    unfold alphaQ_s22_r5
    positivity
  have hprob : ∑ c, alphaQ_s22_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7037679806,492962381980,492962321654,7037616560] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999922772,500000077228,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s25_r3 (c : MME.ReleasedInterior.Split 25) : ℚ :=
  (splitWeight 5 25 3 c : ℚ) / 1000000000000

private def jointExponent_s25_r3 (c : MME.ReleasedInterior.Split 25) : ℕ :=
  [12, 6, 4, 1, 1, 4, 6, 12].getD ((seed 5 25).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s25_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 25 => c.val 0)
        (fun c => (splitWeight 5 25 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 25 => (splitWeight 5 25 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 25) : 0 ≤ alphaQ_s25_r3 c := by
    unfold alphaQ_s25_r3
    positivity
  have hprob : ∑ c, alphaQ_s25_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999976325,500000023675,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![328215607,73614413959,852114739554,73614416322,328214558] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s25_r3 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![6,1,1,6,0] ![1,1,40,40,40] ![12,4,0,4,12] jointExponent_s25_r3 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 25 => c.val 0)
        (fun c => (alphaQ_s25_r3 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s25_r3 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s25_r3, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s25_r4 (c : MME.ReleasedInterior.Split 25) : ℚ :=
  (splitWeight 5 25 4 c : ℚ) / 1000000000000

private def jointExponent_s25_r4 (c : MME.ReleasedInterior.Split 25) : ℕ :=
  [12, 6, 4, 1, 1, 4, 6, 12].getD ((seed 5 25).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s25_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 25 => c.val 0)
        (fun c => (splitWeight 5 25 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 25 => (splitWeight 5 25 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 25) : 0 ≤ alphaQ_s25_r4 c := by
    unfold alphaQ_s25_r4
    positivity
  have hprob : ∑ c, alphaQ_s25_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999999250,500000000750,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![328249472,70619138388,858105223059,70619140822,328248259] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s25_r5 (c : MME.ReleasedInterior.Split 25) : ℚ :=
  (splitWeight 5 25 5 c : ℚ) / 1000000000000

private def jointExponent_s25_r5 (c : MME.ReleasedInterior.Split 25) : ℕ :=
  [12, 6, 4, 1, 1, 4, 6, 12].getD ((seed 5 25).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s25_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 25 => c.val 0)
        (fun c => (splitWeight 5 25 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 25 => (splitWeight 5 25 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 25) : 0 ≤ alphaQ_s25_r5 c := by
    unfold alphaQ_s25_r5
    positivity
  have hprob : ∑ c, alphaQ_s25_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999987285,500000012715,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![325089922,73635593783,852078635661,73635591569,325089065] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s25_r5 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![6,1,1,6,0] ![1,1,40,40,40] ![12,4,0,4,12] jointExponent_s25_r5 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 25 => c.val 0)
        (fun c => (alphaQ_s25_r5 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s25_r5 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s25_r5, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s26_r0 (c : MME.ReleasedInterior.Split 26) : ℚ :=
  (splitWeight 5 26 0 c : ℚ) / 1000000000000

private def jointExponent_s26_r0 (c : MME.ReleasedInterior.Split 26) : ℕ :=
  [9, 7, 6, 2, 3, 3, 2, 6, 7, 9].getD ((seed 5 26).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s26_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 26 => c.val 0)
        (fun c => (splitWeight 5 26 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 26 => (splitWeight 5 26 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 26) : 0 ≤ alphaQ_s26_r0 c := by
    unfold alphaQ_s26_r0
    positivity
  have hprob : ∑ c, alphaQ_s26_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![13770794206,486229197466,486229205592,13770802736,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![12679514217,487320488166,487320512992,12679484625,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 26 1 c : ℚ) / 1000000000000

private def jointExponent_s26_r1 (c : MME.ReleasedInterior.Split 26) : ℕ :=
  [9, 7, 7, 2, 3, 3, 2, 7, 7, 9].getD ((seed 5 26).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s26_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 26 => c.val 0)
        (fun c => (splitWeight 5 26 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 26 => (splitWeight 5 26 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 26) : 0 ≤ alphaQ_s26_r1 c := by
    unfold alphaQ_s26_r1
    positivity
  have hprob : ∑ c, alphaQ_s26_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![13160082828,486839910499,486839902155,13160104518,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![12247271393,487752730324,487752759630,12247238653,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 26 4 c : ℚ) / 1000000000000

private def jointExponent_s26_r4 (c : MME.ReleasedInterior.Split 26) : ℕ :=
  [9, 7, 7, 2, 3, 3, 2, 7, 7, 9].getD ((seed 5 26).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s26_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 26 => c.val 0)
        (fun c => (splitWeight 5 26 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 26 => (splitWeight 5 26 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 26) : 0 ≤ alphaQ_s26_r4 c := by
    unfold alphaQ_s26_r4
    positivity
  have hprob : ∑ c, alphaQ_s26_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![12392164674,487607829320,487607824408,12392181598,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![12956983925,487043018258,487043037100,12956960717,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 26 5 c : ℚ) / 1000000000000

private def jointExponent_s26_r5 (c : MME.ReleasedInterior.Split 26) : ℕ :=
  [9, 6, 7, 2, 3, 3, 2, 7, 6, 9].getD ((seed 5 26).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s26_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 26 => c.val 0)
        (fun c => (splitWeight 5 26 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 26 => (splitWeight 5 26 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 26) : 0 ≤ alphaQ_s26_r5 c := by
    unfold alphaQ_s26_r5
    positivity
  have hprob : ∑ c, alphaQ_s26_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![12849109237,487150883218,487150881077,12849126468,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![13575859651,486424143848,486424160109,13575836392,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s27_r2 (c : MME.ReleasedInterior.Split 27) : ℚ :=
  (splitWeight 5 27 2 c : ℚ) / 1000000000000

private def jointExponent_s27_r2 (c : MME.ReleasedInterior.Split 27) : ℕ :=
  [6, 3, 7, 9, 2, 2, 9, 7, 3, 6].getD ((seed 5 27).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s27_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 27 => c.val 0)
        (fun c => (splitWeight 5 27 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 27 => (splitWeight 5 27 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 27) : 0 ≤ alphaQ_s27_r2 c := by
    unfold alphaQ_s27_r2
    positivity
  have hprob : ∑ c, alphaQ_s27_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![13777572532,486222606187,486223042330,13776778951,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![12747581400,487252316026,487251701589,12748400985,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 27 3 c : ℚ) / 1000000000000

private def jointExponent_s27_r3 (c : MME.ReleasedInterior.Split 27) : ℕ :=
  [7, 3, 7, 9, 2, 2, 9, 7, 3, 7].getD ((seed 5 27).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s27_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 27 => c.val 0)
        (fun c => (splitWeight 5 27 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 27 => (splitWeight 5 27 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 27) : 0 ≤ alphaQ_s27_r3 c := by
    unfold alphaQ_s27_r3
    positivity
  have hprob : ∑ c, alphaQ_s27_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![13161908089,486838260013,486838705308,13161126590,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![12312359929,487687570815,487686914967,12313154289,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s27_r4 (c : MME.ReleasedInterior.Split 27) : ℚ :=
  (splitWeight 5 27 4 c : ℚ) / 1000000000000

private def jointExponent_s27_r4 (c : MME.ReleasedInterior.Split 27) : ℕ :=
  [7, 3, 6, 9, 2, 2, 9, 6, 3, 7].getD ((seed 5 27).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s27_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 27 => c.val 0)
        (fun c => (splitWeight 5 27 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 27 => (splitWeight 5 27 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 27) : 0 ≤ alphaQ_s27_r4 c := by
    unfold alphaQ_s27_r4
    positivity
  have hprob : ∑ c, alphaQ_s27_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![12851195399,487148875654,487148859617,12851069330,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![13660711909,486339320277,486339140421,13660827393,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 27 5 c : ℚ) / 1000000000000

private def jointExponent_s27_r5 (c : MME.ReleasedInterior.Split 27) : ℕ :=
  [7, 3, 7, 9, 2, 2, 9, 7, 3, 7].getD ((seed 5 27).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s27_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 27 => c.val 0)
        (fun c => (splitWeight 5 27 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 27 => (splitWeight 5 27 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 27) : 0 ≤ alphaQ_s27_r5 c := by
    unfold alphaQ_s27_r5
    positivity
  have hprob : ∑ c, alphaQ_s27_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![12403868904,487596203991,487596223975,12403703130,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![13041927501,486958098366,486957895031,13042079102,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s28_r1 (c : MME.ReleasedInterior.Split 28) : ℚ :=
  (splitWeight 5 28 1 c : ℚ) / 1000000000000

private def jointExponent_s28_r1 (c : MME.ReleasedInterior.Split 28) : ℕ :=
  [6, 1, 4, 12, 12, 4, 1, 6].getD ((seed 5 28).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s28_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 28 => c.val 0)
        (fun c => (splitWeight 5 28 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 28 => (splitWeight 5 28 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 28) : 0 ≤ alphaQ_s28_r1 c := by
    unfold alphaQ_s28_r1
    positivity
  have hprob : ∑ c, alphaQ_s28_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![330559803,77758872148,843821052557,77758913210,330602282] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999852915,500000147085,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 28 4 c : ℚ) / 1000000000000

private def jointExponent_s28_r4 (c : MME.ReleasedInterior.Split 28) : ℕ :=
  [6, 1, 4, 12, 12, 4, 1, 6].getD ((seed 5 28).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s28_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 28 => c.val 0)
        (fun c => (splitWeight 5 28 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 28 => (splitWeight 5 28 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 28) : 0 ≤ alphaQ_s28_r4 c := by
    unfold alphaQ_s28_r4
    positivity
  have hprob : ∑ c, alphaQ_s28_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![328578825,77718877697,843905133719,77718869089,328540670] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000069546,499999930454,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s28_r5 (c : MME.ReleasedInterior.Split 28) : ℚ :=
  (splitWeight 5 28 5 c : ℚ) / 1000000000000

private def jointExponent_s28_r5 (c : MME.ReleasedInterior.Split 28) : ℕ :=
  [6, 1, 4, 12, 12, 4, 1, 6].getD ((seed 5 28).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s28_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 28 => c.val 0)
        (fun c => (splitWeight 5 28 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 28 => (splitWeight 5 28 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 28) : 0 ≤ alphaQ_s28_r5 c := by
    unfold alphaQ_s28_r5
    positivity
  have hprob : ∑ c, alphaQ_s28_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![328261047,74881130595,849581247944,74881163811,328196603] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000014768,499999985232,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s28_r5 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![6,1,1,6,0] ![12,4,0,4,12] ![1,1,40,40,40] jointExponent_s28_r5 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 28 => c.val 0)
        (fun c => (alphaQ_s28_r5 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s28_r5 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s28_r5, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s31_r0 (c : MME.ReleasedInterior.Split 31) : ℚ :=
  (splitWeight 5 31 0 c : ℚ) / 1000000000000

private def jointExponent_s31_r0 (c : MME.ReleasedInterior.Split 31) : ℕ :=
  [12, 6, 4, 1, 1, 4, 6, 12].getD ((seed 5 31).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s31_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 31 => c.val 0)
        (fun c => (splitWeight 5 31 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 31 => (splitWeight 5 31 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 31) : 0 ≤ alphaQ_s31_r0 c := by
    unfold alphaQ_s31_r0
    positivity
  have hprob : ∑ c, alphaQ_s31_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![327402057,80464832349,838415523790,80464840915,327400889] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999984334,500000015666,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s31_r0 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![12,4,0,4,12] ![12,4,0,4,12] ![1,1,40,40,40] jointExponent_s31_r0 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 31 => c.val 0)
        (fun c => (alphaQ_s31_r0 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s31_r0 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s31_r0, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s31_r1 (c : MME.ReleasedInterior.Split 31) : ℚ :=
  (splitWeight 5 31 1 c : ℚ) / 1000000000000

private def jointExponent_s31_r1 (c : MME.ReleasedInterior.Split 31) : ℕ :=
  [12, 6, 4, 1, 1, 4, 6, 12].getD ((seed 5 31).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s31_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 31 => c.val 0)
        (fun c => (splitWeight 5 31 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 31 => (splitWeight 5 31 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 31) : 0 ≤ alphaQ_s31_r1 c := by
    unfold alphaQ_s31_r1
    positivity
  have hprob : ∑ c, alphaQ_s31_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![324737443,77736638877,843877242616,77736644343,324736721] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999990294,500000009706,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s31_r1 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![12,4,0,4,12] ![12,4,0,4,12] ![1,1,40,40,40] jointExponent_s31_r1 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 31 => c.val 0)
        (fun c => (alphaQ_s31_r1 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s31_r1 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s31_r1, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s31_r2 (c : MME.ReleasedInterior.Split 31) : ℚ :=
  (splitWeight 5 31 2 c : ℚ) / 1000000000000

private def jointExponent_s31_r2 (c : MME.ReleasedInterior.Split 31) : ℕ :=
  [12, 6, 4, 1, 1, 4, 6, 12].getD ((seed 5 31).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s31_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 31 => c.val 0)
        (fun c => (splitWeight 5 31 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 31 => (splitWeight 5 31 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 31) : 0 ≤ alphaQ_s31_r2 c := by
    unfold alphaQ_s31_r2
    positivity
  have hprob : ∑ c, alphaQ_s31_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![328586029,80541962055,838258893809,80541973645,328584462] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999981072,500000018928,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s32_r1 (c : MME.ReleasedInterior.Split 32) : ℚ :=
  (splitWeight 5 32 1 c : ℚ) / 1000000000000

private def jointExponent_s32_r1 (c : MME.ReleasedInterior.Split 32) : ℕ :=
  [12, 5, 3, 5, 1, 5, 3, 5, 12].getD ((seed 5 32).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s32_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 32 => c.val 0)
        (fun c => (splitWeight 5 32 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 32 => (splitWeight 5 32 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 32) : 0 ≤ alphaQ_s32_r1 c := by
    unfold alphaQ_s32_r1
    positivity
  have hprob : ∑ c, alphaQ_s32_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![335754372,79184380156,840959763702,79184346088,335755682] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![180642952294,638713988799,180643058907,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s32_r3 (c : MME.ReleasedInterior.Split 32) : ℚ :=
  (splitWeight 5 32 3 c : ℚ) / 1000000000000

private def jointExponent_s32_r3 (c : MME.ReleasedInterior.Split 32) : ℕ :=
  [12, 5, 3, 5, 1, 5, 3, 5, 12].getD ((seed 5 32).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s32_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 32 => c.val 0)
        (fun c => (splitWeight 5 32 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 32 => (splitWeight 5 32 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 32) : 0 ≤ alphaQ_s32_r3 c := by
    unfold alphaQ_s32_r3
    positivity
  have hprob : ∑ c, alphaQ_s32_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![335755858,79188067971,840952385304,79188036968,335753899] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![180600961502,638798147680,180600890818,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s32_r3 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![12,4,0,4,12] ![12,4,0,4,12] ![3,1,3,40,40] jointExponent_s32_r3 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 32 => c.val 0)
        (fun c => (alphaQ_s32_r3 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s32_r3 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s32_r3, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s32_r4 (c : MME.ReleasedInterior.Split 32) : ℚ :=
  (splitWeight 5 32 4 c : ℚ) / 1000000000000

private def jointExponent_s32_r4 (c : MME.ReleasedInterior.Split 32) : ℕ :=
  [12, 5, 3, 5, 1, 5, 3, 5, 12].getD ((seed 5 32).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s32_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 32 => c.val 0)
        (fun c => (splitWeight 5 32 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 32 => (splitWeight 5 32 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 32) : 0 ≤ alphaQ_s32_r4 c := by
    unfold alphaQ_s32_r4
    positivity
  have hprob : ∑ c, alphaQ_s32_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![336184767,79862757452,839602147902,79862726929,336182950] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![181881740329,636236410808,181881848863,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s32_r5 (c : MME.ReleasedInterior.Split 32) : ℚ :=
  (splitWeight 5 32 5 c : ℚ) / 1000000000000

private def jointExponent_s32_r5 (c : MME.ReleasedInterior.Split 32) : ℕ :=
  [12, 5, 3, 5, 1, 5, 3, 5, 12].getD ((seed 5 32).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s32_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 32 => c.val 0)
        (fun c => (splitWeight 5 32 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 32 => (splitWeight 5 32 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 32) : 0 ≤ alphaQ_s32_r5 c := by
    unfold alphaQ_s32_r5
    positivity
  have hprob : ∑ c, alphaQ_s32_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![336218518,79865339433,839596916296,79865308333,336217420] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![181830879667,636338314094,181830806239,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s32_r5 ha hprob 0 1
    (by decide) p q hp hq hpmass hqmass ![12,4,0,4,12] ![12,4,0,4,12] ![3,1,3,40,40] jointExponent_s32_r5 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 32 => c.val 0)
        (fun c => (alphaQ_s32_r5 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s32_r5 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s32_r5, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s33_r0 (c : MME.ReleasedInterior.Split 33) : ℚ :=
  (splitWeight 5 33 0 c : ℚ) / 1000000000000

private def jointExponent_s33_r0 (c : MME.ReleasedInterior.Split 33) : ℕ :=
  [12, 4, 1, 6, 6, 1, 4, 12].getD ((seed 5 33).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s33_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 33 => c.val 0)
        (fun c => (splitWeight 5 33 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 33 => (splitWeight 5 33 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 33) : 0 ≤ alphaQ_s33_r0 c := by
    unfold alphaQ_s33_r0
    positivity
  have hprob : ∑ c, alphaQ_s33_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![329930355,80559657146,838220834795,80559648306,329929398] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000020042,499999979958,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s33_r0 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![12,4,0,4,12] ![12,4,0,4,12] ![1,1,40,40,40] jointExponent_s33_r0 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 33 => c.val 0)
        (fun c => (alphaQ_s33_r0 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s33_r0 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s33_r0, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s33_r2 (c : MME.ReleasedInterior.Split 33) : ℚ :=
  (splitWeight 5 33 2 c : ℚ) / 1000000000000

private def jointExponent_s33_r2 (c : MME.ReleasedInterior.Split 33) : ℕ :=
  [12, 4, 1, 6, 6, 1, 4, 12].getD ((seed 5 33).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s33_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 33 => c.val 0)
        (fun c => (splitWeight 5 33 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 33 => (splitWeight 5 33 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 33) : 0 ≤ alphaQ_s33_r2 c := by
    unfold alphaQ_s33_r2
    positivity
  have hprob : ∑ c, alphaQ_s33_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![328631665,80486830216,838369100329,80486815739,328622051] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000037893,499999962107,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 33 3 c : ℚ) / 1000000000000

private def jointExponent_s33_r3 (c : MME.ReleasedInterior.Split 33) : ℕ :=
  [12, 4, 1, 6, 6, 1, 4, 12].getD ((seed 5 33).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s33_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 33 => c.val 0)
        (fun c => (splitWeight 5 33 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 33 => (splitWeight 5 33 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 33) : 0 ≤ alphaQ_s33_r3 c := by
    unfold alphaQ_s33_r3
    positivity
  have hprob : ∑ c, alphaQ_s33_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![326460290,77743722182,843859639742,77743724332,326453454] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000007573,499999992427,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s36_r0 (c : MME.ReleasedInterior.Split 36) : ℚ :=
  (splitWeight 5 36 0 c : ℚ) / 1000000000000

private def jointExponent_s36_r0 (c : MME.ReleasedInterior.Split 36) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 5 36).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s36_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 36 => c.val 0)
        (fun c => (splitWeight 5 36 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 36 => (splitWeight 5 36 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 36) : 0 ≤ alphaQ_s36_r0 c := by
    unfold alphaQ_s36_r0
    positivity
  have hprob : ∑ c, alphaQ_s36_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7348814381,492651259924,492650953736,7348971959] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000087317,499999912683,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s36_r1 (c : MME.ReleasedInterior.Split 36) : ℚ :=
  (splitWeight 5 36 1 c : ℚ) / 1000000000000

private def jointExponent_s36_r1 (c : MME.ReleasedInterior.Split 36) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 5 36).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s36_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 36 => c.val 0)
        (fun c => (splitWeight 5 36 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 36 => (splitWeight 5 36 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 36) : 0 ≤ alphaQ_s36_r1 c := by
    unfold alphaQ_s36_r1
    positivity
  have hprob : ∑ c, alphaQ_s36_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7252147865,492747933302,492747565452,7252353381] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000095607,499999904393,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 36 2 c : ℚ) / 1000000000000

private def jointExponent_s36_r2 (c : MME.ReleasedInterior.Split 36) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 5 36).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s36_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 36 => c.val 0)
        (fun c => (splitWeight 5 36 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 36 => (splitWeight 5 36 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 36) : 0 ≤ alphaQ_s36_r2 c := by
    unfold alphaQ_s36_r2
    positivity
  have hprob : ∑ c, alphaQ_s36_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7365940214,492634133194,492633839477,7366087115] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000083551,499999916449,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 36 3 c : ℚ) / 1000000000000

private def jointExponent_s36_r3 (c : MME.ReleasedInterior.Split 36) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 5 36).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s36_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 36 => c.val 0)
        (fun c => (splitWeight 5 36 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 36 => (splitWeight 5 36 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 36) : 0 ≤ alphaQ_s36_r3 c := by
    unfold alphaQ_s36_r3
    positivity
  have hprob : ∑ c, alphaQ_s36_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7326681872,492673387713,492673095523,7326834892] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000092569,499999907431,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s36_r5 (c : MME.ReleasedInterior.Split 36) : ℚ :=
  (splitWeight 5 36 5 c : ℚ) / 1000000000000

private def jointExponent_s36_r5 (c : MME.ReleasedInterior.Split 36) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 5 36).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s36_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 36 => c.val 0)
        (fun c => (splitWeight 5 36 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 36 => (splitWeight 5 36 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 36) : 0 ≤ alphaQ_s36_r5 c := by
    unfold alphaQ_s36_r5
    positivity
  have hprob : ∑ c, alphaQ_s36_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7309813571,492686240771,492689941361,7314004297] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500008877134,499991122866,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 37 0 c : ℚ) / 1000000000000

private def jointExponent_s37_r0 (c : MME.ReleasedInterior.Split 37) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 5 37).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s37_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 37 => c.val 0)
        (fun c => (splitWeight 5 37 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 37 => (splitWeight 5 37 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 37) : 0 ≤ alphaQ_s37_r0 c := by
    unfold alphaQ_s37_r0
    positivity
  have hprob : ∑ c, alphaQ_s37_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7368453187,492631543571,492631568563,7368434679] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999995980,500000004020,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s37_r1 (c : MME.ReleasedInterior.Split 37) : ℚ :=
  (splitWeight 5 37 1 c : ℚ) / 1000000000000

private def jointExponent_s37_r1 (c : MME.ReleasedInterior.Split 37) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 5 37).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s37_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 37 => c.val 0)
        (fun c => (splitWeight 5 37 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 37 => (splitWeight 5 37 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 37) : 0 ≤ alphaQ_s37_r1 c := by
    unfold alphaQ_s37_r1
    positivity
  have hprob : ∑ c, alphaQ_s37_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7327013105,492672964811,492673025158,7326996926] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000017067,499999982933,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 37 2 c : ℚ) / 1000000000000

private def jointExponent_s37_r2 (c : MME.ReleasedInterior.Split 37) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 5 37).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s37_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 37 => c.val 0)
        (fun c => (splitWeight 5 37 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 37 => (splitWeight 5 37 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 37) : 0 ≤ alphaQ_s37_r2 c := by
    unfold alphaQ_s37_r2
    positivity
  have hprob : ∑ c, alphaQ_s37_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7353001177,492646992782,492647016714,7352989327] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999999330,500000000670,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 37 3 c : ℚ) / 1000000000000

private def jointExponent_s37_r3 (c : MME.ReleasedInterior.Split 37) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 5 37).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s37_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 37 => c.val 0)
        (fun c => (splitWeight 5 37 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 37 => (splitWeight 5 37 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 37) : 0 ≤ alphaQ_s37_r3 c := by
    unfold alphaQ_s37_r3
    positivity
  have hprob : ∑ c, alphaQ_s37_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7255287487,492744720956,492744618796,7255372761] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000023514,499999976486,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 37 4 c : ℚ) / 1000000000000

private def jointExponent_s37_r4 (c : MME.ReleasedInterior.Split 37) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 5 37).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s37_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 37 => c.val 0)
        (fun c => (splitWeight 5 37 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 37 => (splitWeight 5 37 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 37) : 0 ≤ alphaQ_s37_r4 c := by
    unfold alphaQ_s37_r4
    positivity
  have hprob : ∑ c, alphaQ_s37_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7316081859,492683929170,492683893382,7316095589] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999995292,500000004708,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s40_r0 (c : MME.ReleasedInterior.Split 40) : ℚ :=
  (splitWeight 5 40 0 c : ℚ) / 1000000000000

private def jointExponent_s40_r0 (c : MME.ReleasedInterior.Split 40) : ℕ :=
  [3, 1, 1, 3].getD ((seed 5 40).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s40_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 40 => c.val 0)
        (fun c => (splitWeight 5 40 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 40 => (splitWeight 5 40 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 40) : 0 ≤ alphaQ_s40_r0 c := by
    unfold alphaQ_s40_r0
    positivity
  have hprob : ∑ c, alphaQ_s40_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500026308809,499973691191,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499948368092,500051631908,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 40 1 c : ℚ) / 1000000000000

private def jointExponent_s40_r1 (c : MME.ReleasedInterior.Split 40) : ℕ :=
  [3, 1, 1, 3].getD ((seed 5 40).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s40_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 40 => c.val 0)
        (fun c => (splitWeight 5 40 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 40 => (splitWeight 5 40 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 40) : 0 ≤ alphaQ_s40_r1 c := by
    unfold alphaQ_s40_r1
    positivity
  have hprob : ∑ c, alphaQ_s40_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500002277986,499997722014,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499980042721,500019957279,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 40 2 c : ℚ) / 1000000000000

private def jointExponent_s40_r2 (c : MME.ReleasedInterior.Split 40) : ℕ :=
  [3, 1, 1, 3].getD ((seed 5 40).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s40_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 40 => c.val 0)
        (fun c => (splitWeight 5 40 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 40 => (splitWeight 5 40 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 40) : 0 ≤ alphaQ_s40_r2 c := by
    unfold alphaQ_s40_r2
    positivity
  have hprob : ∑ c, alphaQ_s40_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500026371892,499973628108,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499948253876,500051746124,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 40 3 c : ℚ) / 1000000000000

private def jointExponent_s40_r3 (c : MME.ReleasedInterior.Split 40) : ℕ :=
  [3, 1, 1, 3].getD ((seed 5 40).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s40_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 40 => c.val 0)
        (fun c => (splitWeight 5 40 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 40 => (splitWeight 5 40 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 40) : 0 ≤ alphaQ_s40_r3 c := by
    unfold alphaQ_s40_r3
    positivity
  have hprob : ∑ c, alphaQ_s40_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499993497060,500006502940,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500012743484,499987256516,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 40 4 c : ℚ) / 1000000000000

private def jointExponent_s40_r4 (c : MME.ReleasedInterior.Split 40) : ℕ :=
  [3, 1, 1, 3].getD ((seed 5 40).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s40_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 40 => c.val 0)
        (fun c => (splitWeight 5 40 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 40 => (splitWeight 5 40 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 40) : 0 ≤ alphaQ_s40_r4 c := by
    unfold alphaQ_s40_r4
    positivity
  have hprob : ∑ c, alphaQ_s40_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499986536781,500013463219,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500026384587,499973615413,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 5 40 5 c : ℚ) / 1000000000000

private def jointExponent_s40_r5 (c : MME.ReleasedInterior.Split 40) : ℕ :=
  [3, 1, 1, 3].getD ((seed 5 40).splits.idxOf (sourceShape 5 c)) 0

private theorem region_s40_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 40 => c.val 0)
        (fun c => (splitWeight 5 40 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 40 => (splitWeight 5 40 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 40) : 0 ≤ alphaQ_s40_r5 c := by
    unfold alphaQ_s40_r5
    positivity
  have hprob : ∑ c, alphaQ_s40_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499986556732,500013443268,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500026300879,499973699121,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
    (s : Fin 45) (r : Fin 6) (hi : (seed 5 s).boundary = [])
    (hn : 0 < (seed 5 s).region.getD r.val 0) :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split s => c.val 0)
        (fun c => (splitWeight 5 s r c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split s => (splitWeight 5 s r c : ℝ) / 1000000000000) := by
  fin_cases s
  · exact False.elim ((by decide +kernel : (seed 5 0).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 5 1).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 5 2).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 5 3).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 5 4).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 5 5).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 5 6).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 5 7).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 5 8).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 5 9).boundary ≠ []) hi)
  · fin_cases r
    · exact region_s10_r0
    · exact region_s10_r1
    · exact region_s10_r2
    · exact region_s10_r3
    · exact region_s10_r4
    · exact region_s10_r5
  · fin_cases r
    · have hz : (seed 5 11).region.getD 0 0 = 0 := by decide +kernel
      change 0 < (seed 5 11).region.getD 0 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 5 11).region.getD 1 0 = 0 := by decide +kernel
      change 0 < (seed 5 11).region.getD 1 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s11_r2
    · exact region_s11_r3
    · have hz : (seed 5 11).region.getD 4 0 = 0 := by decide +kernel
      change 0 < (seed 5 11).region.getD 4 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s11_r5
  · fin_cases r
    · have hz : (seed 5 12).region.getD 0 0 = 0 := by decide +kernel
      change 0 < (seed 5 12).region.getD 0 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 5 12).region.getD 1 0 = 0 := by decide +kernel
      change 0 < (seed 5 12).region.getD 1 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s12_r2
    · exact region_s12_r3
    · have hz : (seed 5 12).region.getD 4 0 = 0 := by decide +kernel
      change 0 < (seed 5 12).region.getD 4 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s12_r5
  · fin_cases r
    · exact region_s13_r0
    · exact region_s13_r1
    · have hz : (seed 5 13).region.getD 2 0 = 0 := by decide +kernel
      change 0 < (seed 5 13).region.getD 2 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 5 13).region.getD 3 0 = 0 := by decide +kernel
      change 0 < (seed 5 13).region.getD 3 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s13_r4
    · have hz : (seed 5 13).region.getD 5 0 = 0 := by decide +kernel
      change 0 < (seed 5 13).region.getD 5 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
  · fin_cases r
    · exact region_s14_r0
    · exact region_s14_r1
    · have hz : (seed 5 14).region.getD 2 0 = 0 := by decide +kernel
      change 0 < (seed 5 14).region.getD 2 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s14_r3
    · exact region_s14_r4
    · exact region_s14_r5
  · fin_cases r
    · exact region_s15_r0
    · exact region_s15_r1
    · exact region_s15_r2
    · exact region_s15_r3
    · exact region_s15_r4
    · exact region_s15_r5
  · exact False.elim ((by decide +kernel : (seed 5 16).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 5 17).boundary ≠ []) hi)
  · fin_cases r
    · have hz : (seed 5 18).region.getD 0 0 = 0 := by decide +kernel
      change 0 < (seed 5 18).region.getD 0 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 5 18).region.getD 1 0 = 0 := by decide +kernel
      change 0 < (seed 5 18).region.getD 1 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 5 18).region.getD 2 0 = 0 := by decide +kernel
      change 0 < (seed 5 18).region.getD 2 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s18_r3
    · exact region_s18_r4
    · exact region_s18_r5
  · fin_cases r
    · have hz : (seed 5 19).region.getD 0 0 = 0 := by decide +kernel
      change 0 < (seed 5 19).region.getD 0 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 5 19).region.getD 1 0 = 0 := by decide +kernel
      change 0 < (seed 5 19).region.getD 1 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s19_r2
    · exact region_s19_r3
    · exact region_s19_r4
    · exact region_s19_r5
  · fin_cases r
    · exact region_s20_r0
    · exact region_s20_r1
    · exact region_s20_r2
    · exact region_s20_r3
    · have hz : (seed 5 20).region.getD 4 0 = 0 := by decide +kernel
      change 0 < (seed 5 20).region.getD 4 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 5 20).region.getD 5 0 = 0 := by decide +kernel
      change 0 < (seed 5 20).region.getD 5 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
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
    · have hz : (seed 5 22).region.getD 3 0 = 0 := by decide +kernel
      change 0 < (seed 5 22).region.getD 3 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s22_r4
    · exact region_s22_r5
  · exact False.elim ((by decide +kernel : (seed 5 23).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 5 24).boundary ≠ []) hi)
  · fin_cases r
    · have hz : (seed 5 25).region.getD 0 0 = 0 := by decide +kernel
      change 0 < (seed 5 25).region.getD 0 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 5 25).region.getD 1 0 = 0 := by decide +kernel
      change 0 < (seed 5 25).region.getD 1 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 5 25).region.getD 2 0 = 0 := by decide +kernel
      change 0 < (seed 5 25).region.getD 2 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s25_r3
    · exact region_s25_r4
    · exact region_s25_r5
  · fin_cases r
    · exact region_s26_r0
    · exact region_s26_r1
    · have hz : (seed 5 26).region.getD 2 0 = 0 := by decide +kernel
      change 0 < (seed 5 26).region.getD 2 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 5 26).region.getD 3 0 = 0 := by decide +kernel
      change 0 < (seed 5 26).region.getD 3 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s26_r4
    · exact region_s26_r5
  · fin_cases r
    · have hz : (seed 5 27).region.getD 0 0 = 0 := by decide +kernel
      change 0 < (seed 5 27).region.getD 0 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 5 27).region.getD 1 0 = 0 := by decide +kernel
      change 0 < (seed 5 27).region.getD 1 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s27_r2
    · exact region_s27_r3
    · exact region_s27_r4
    · exact region_s27_r5
  · fin_cases r
    · have hz : (seed 5 28).region.getD 0 0 = 0 := by decide +kernel
      change 0 < (seed 5 28).region.getD 0 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s28_r1
    · have hz : (seed 5 28).region.getD 2 0 = 0 := by decide +kernel
      change 0 < (seed 5 28).region.getD 2 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 5 28).region.getD 3 0 = 0 := by decide +kernel
      change 0 < (seed 5 28).region.getD 3 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s28_r4
    · exact region_s28_r5
  · exact False.elim ((by decide +kernel : (seed 5 29).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 5 30).boundary ≠ []) hi)
  · fin_cases r
    · exact region_s31_r0
    · exact region_s31_r1
    · exact region_s31_r2
    · have hz : (seed 5 31).region.getD 3 0 = 0 := by decide +kernel
      change 0 < (seed 5 31).region.getD 3 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 5 31).region.getD 4 0 = 0 := by decide +kernel
      change 0 < (seed 5 31).region.getD 4 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 5 31).region.getD 5 0 = 0 := by decide +kernel
      change 0 < (seed 5 31).region.getD 5 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
  · fin_cases r
    · have hz : (seed 5 32).region.getD 0 0 = 0 := by decide +kernel
      change 0 < (seed 5 32).region.getD 0 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s32_r1
    · have hz : (seed 5 32).region.getD 2 0 = 0 := by decide +kernel
      change 0 < (seed 5 32).region.getD 2 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s32_r3
    · exact region_s32_r4
    · exact region_s32_r5
  · fin_cases r
    · exact region_s33_r0
    · have hz : (seed 5 33).region.getD 1 0 = 0 := by decide +kernel
      change 0 < (seed 5 33).region.getD 1 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s33_r2
    · exact region_s33_r3
    · have hz : (seed 5 33).region.getD 4 0 = 0 := by decide +kernel
      change 0 < (seed 5 33).region.getD 4 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 5 33).region.getD 5 0 = 0 := by decide +kernel
      change 0 < (seed 5 33).region.getD 5 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
  · exact False.elim ((by decide +kernel : (seed 5 34).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 5 35).boundary ≠ []) hi)
  · fin_cases r
    · exact region_s36_r0
    · exact region_s36_r1
    · exact region_s36_r2
    · exact region_s36_r3
    · have hz : (seed 5 36).region.getD 4 0 = 0 := by decide +kernel
      change 0 < (seed 5 36).region.getD 4 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s36_r5
  · fin_cases r
    · exact region_s37_r0
    · exact region_s37_r1
    · exact region_s37_r2
    · exact region_s37_r3
    · exact region_s37_r4
    · have hz : (seed 5 37).region.getD 5 0 = 0 := by decide +kernel
      change 0 < (seed 5 37).region.getD 5 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
  · exact False.elim ((by decide +kernel : (seed 5 38).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 5 39).boundary ≠ []) hi)
  · fin_cases r
    · exact region_s40_r0
    · exact region_s40_r1
    · exact region_s40_r2
    · exact region_s40_r3
    · exact region_s40_r4
    · exact region_s40_r5
  · exact False.elim ((by decide +kernel : (seed 5 41).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 5 42).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 5 43).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 5 44).boundary ≠ []) hi)


#print axioms solution
