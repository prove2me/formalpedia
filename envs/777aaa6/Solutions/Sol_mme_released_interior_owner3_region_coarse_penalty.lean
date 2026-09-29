-- Prove2me | solution 1 for mme_released_interior_owner3_region_coarse_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T07:19:13.258456+00:00
-- url     : https://prove2.me/submissions/831b1058-c6b5-45f9-b64f-2fbe2b33b110

import Theorems.Thm_mme_rational_coarse_penalty_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.RecursiveThinSplit MME.ReleasedInterior

private def alphaQ_s10_r0 (c : MME.ReleasedInterior.Split 10) : ℚ :=
  (splitWeight 3 10 0 c : ℚ) / 1000000000000

private def jointExponent_s10_r0 (c : MME.ReleasedInterior.Split 10) : ℕ :=
  [3, 1, 1, 3].getD ((seed 3 10).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s10_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 10 => c.val 0)
        (fun c => (splitWeight 3 10 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 10 => (splitWeight 3 10 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 10) : 0 ≤ alphaQ_s10_r0 c := by
    unfold alphaQ_s10_r0
    positivity
  have hprob : ∑ c, alphaQ_s10_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499660560548,500339439452,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500347696193,499652303807,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 10 1 c : ℚ) / 1000000000000

private def jointExponent_s10_r1 (c : MME.ReleasedInterior.Split 10) : ℕ :=
  [3, 1, 1, 3].getD ((seed 3 10).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s10_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 10 => c.val 0)
        (fun c => (splitWeight 3 10 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 10 => (splitWeight 3 10 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 10) : 0 ≤ alphaQ_s10_r1 c := by
    unfold alphaQ_s10_r1
    positivity
  have hprob : ∑ c, alphaQ_s10_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500356859505,499643140495,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499656234071,500343765929,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 10 2 c : ℚ) / 1000000000000

private def jointExponent_s10_r2 (c : MME.ReleasedInterior.Split 10) : ℕ :=
  [3, 1, 1, 3].getD ((seed 3 10).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s10_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 10 => c.val 0)
        (fun c => (splitWeight 3 10 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 10 => (splitWeight 3 10 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 10) : 0 ≤ alphaQ_s10_r2 c := by
    unfold alphaQ_s10_r2
    positivity
  have hprob : ∑ c, alphaQ_s10_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500270115771,499729884229,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499858125883,500141874117,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 10 3 c : ℚ) / 1000000000000

private def jointExponent_s10_r3 (c : MME.ReleasedInterior.Split 10) : ℕ :=
  [3, 1, 1, 3].getD ((seed 3 10).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s10_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 10 => c.val 0)
        (fun c => (splitWeight 3 10 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 10 => (splitWeight 3 10 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 10) : 0 ≤ alphaQ_s10_r3 c := by
    unfold alphaQ_s10_r3
    positivity
  have hprob : ∑ c, alphaQ_s10_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500002163328,499997836672,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500002162479,499997837521,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 10 4 c : ℚ) / 1000000000000

private def jointExponent_s10_r4 (c : MME.ReleasedInterior.Split 10) : ℕ :=
  [3, 1, 1, 3].getD ((seed 3 10).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s10_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 10 => c.val 0)
        (fun c => (splitWeight 3 10 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 10 => (splitWeight 3 10 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 10) : 0 ≤ alphaQ_s10_r4 c := by
    unfold alphaQ_s10_r4
    positivity
  have hprob : ∑ c, alphaQ_s10_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499859585732,500140414268,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500267424229,499732575771,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 10 5 c : ℚ) / 1000000000000

private def jointExponent_s10_r5 (c : MME.ReleasedInterior.Split 10) : ℕ :=
  [3, 1, 1, 3].getD ((seed 3 10).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s10_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 10 => c.val 0)
        (fun c => (splitWeight 3 10 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 10 => (splitWeight 3 10 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 10) : 0 ≤ alphaQ_s10_r5 c := by
    unfold alphaQ_s10_r5
    positivity
  have hprob : ∑ c, alphaQ_s10_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500002112053,499997887947,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500002112846,499997887154,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s11_r3 (c : MME.ReleasedInterior.Split 11) : ℚ :=
  (splitWeight 3 11 3 c : ℚ) / 1000000000000

private def jointExponent_s11_r3 (c : MME.ReleasedInterior.Split 11) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 3 11).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s11_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 11 => c.val 0)
        (fun c => (splitWeight 3 11 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 11 => (splitWeight 3 11 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 11) : 0 ≤ alphaQ_s11_r3 c := by
    unfold alphaQ_s11_r3
    positivity
  have hprob : ∑ c, alphaQ_s11_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999978755,500000021245,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,6583874821,493416107444,493416210955,6583806780] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s11_r4 (c : MME.ReleasedInterior.Split 11) : ℚ :=
  (splitWeight 3 11 4 c : ℚ) / 1000000000000

private def jointExponent_s11_r4 (c : MME.ReleasedInterior.Split 11) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 3 11).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s11_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 11 => c.val 0)
        (fun c => (splitWeight 3 11 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 11 => (splitWeight 3 11 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 11) : 0 ≤ alphaQ_s11_r4 c := by
    unfold alphaQ_s11_r4
    positivity
  have hprob : ∑ c, alphaQ_s11_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999971773,500000028227,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,6632447620,493367566346,493367576085,6632409949] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 11 5 c : ℚ) / 1000000000000

private def jointExponent_s11_r5 (c : MME.ReleasedInterior.Split 11) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 3 11).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s11_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 11 => c.val 0)
        (fun c => (splitWeight 3 11 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 11 => (splitWeight 3 11 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 11) : 0 ≤ alphaQ_s11_r5 c := by
    unfold alphaQ_s11_r5
    positivity
  have hprob : ∑ c, alphaQ_s11_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999981903,500000018097,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,6608660733,493391324089,493391413907,6608601271] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s12_r3 (c : MME.ReleasedInterior.Split 12) : ℚ :=
  (splitWeight 3 12 3 c : ℚ) / 1000000000000

private def jointExponent_s12_r3 (c : MME.ReleasedInterior.Split 12) : ℕ :=
  [12, 6, 4, 1, 1, 4, 6, 12].getD ((seed 3 12).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s12_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 12 => c.val 0)
        (fun c => (splitWeight 3 12 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 12 => (splitWeight 3 12 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 12) : 0 ≤ alphaQ_s12_r3 c := by
    unfold alphaQ_s12_r3
    positivity
  have hprob : ∑ c, alphaQ_s12_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000002208,499999997792,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![326238039,73586721139,852174078444,73586723636,326238742] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s12_r4 (c : MME.ReleasedInterior.Split 12) : ℚ :=
  (splitWeight 3 12 4 c : ℚ) / 1000000000000

private def jointExponent_s12_r4 (c : MME.ReleasedInterior.Split 12) : ℕ :=
  [12, 6, 4, 1, 1, 4, 6, 12].getD ((seed 3 12).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s12_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 12 => c.val 0)
        (fun c => (splitWeight 3 12 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 12 => (splitWeight 3 12 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 12) : 0 ≤ alphaQ_s12_r4 c := by
    unfold alphaQ_s12_r4
    positivity
  have hprob : ∑ c, alphaQ_s12_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999995716,500000004284,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![325700737,70601096152,858146406766,70601093200,325703145] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 12 5 c : ℚ) / 1000000000000

private def jointExponent_s12_r5 (c : MME.ReleasedInterior.Split 12) : ℕ :=
  [12, 6, 4, 1, 1, 4, 6, 12].getD ((seed 3 12).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s12_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 12 => c.val 0)
        (fun c => (splitWeight 3 12 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 12 => (splitWeight 3 12 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 12) : 0 ≤ alphaQ_s12_r5 c := by
    unfold alphaQ_s12_r5
    positivity
  have hprob : ∑ c, alphaQ_s12_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999985868,500000014132,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![323436585,73599464323,852154195099,73599466648,323437345] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 13 0 c : ℚ) / 1000000000000

private def jointExponent_s13_r0 (c : MME.ReleasedInterior.Split 13) : ℕ :=
  [12, 6, 4, 1, 1, 4, 6, 12].getD ((seed 3 13).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s13_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 13 => c.val 0)
        (fun c => (splitWeight 3 13 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 13 => (splitWeight 3 13 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 13) : 0 ≤ alphaQ_s13_r0 c := by
    unfold alphaQ_s13_r0
    positivity
  have hprob : ∑ c, alphaQ_s13_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999991933,500000008067,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![325681006,77659656399,844029320669,77659661573,325680353] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 13 1 c : ℚ) / 1000000000000

private def jointExponent_s13_r1 (c : MME.ReleasedInterior.Split 13) : ℕ :=
  [12, 6, 4, 1, 1, 4, 6, 12].getD ((seed 3 13).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s13_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 13 => c.val 0)
        (fun c => (splitWeight 3 13 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 13 => (splitWeight 3 13 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 13) : 0 ≤ alphaQ_s13_r1 c := by
    unfold alphaQ_s13_r1
    positivity
  have hprob : ∑ c, alphaQ_s13_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999993476,500000006524,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![324006152,74862913608,849626157577,74862919473,324003190] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s13_r2 (c : MME.ReleasedInterior.Split 13) : ℚ :=
  (splitWeight 3 13 2 c : ℚ) / 1000000000000

private def jointExponent_s13_r2 (c : MME.ReleasedInterior.Split 13) : ℕ :=
  [12, 6, 4, 1, 1, 4, 6, 12].getD ((seed 3 13).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s13_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 13 => c.val 0)
        (fun c => (splitWeight 3 13 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 13 => (splitWeight 3 13 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 13) : 0 ≤ alphaQ_s13_r2 c := by
    unfold alphaQ_s13_r2
    positivity
  have hprob : ∑ c, alphaQ_s13_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999995421,500000004579,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![327304123,77707830638,843929728218,77707833042,327303979] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s14_r0 (c : MME.ReleasedInterior.Split 14) : ℚ :=
  (splitWeight 3 14 0 c : ℚ) / 1000000000000

private def jointExponent_s14_r0 (c : MME.ReleasedInterior.Split 14) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 3 14).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s14_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 14 => c.val 0)
        (fun c => (splitWeight 3 14 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 14 => (splitWeight 3 14 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 14) : 0 ≤ alphaQ_s14_r0 c := by
    unfold alphaQ_s14_r0
    positivity
  have hprob : ∑ c, alphaQ_s14_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999470910,500000529090,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,7069962170,492929872862,492932074320,7068090648] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 14 1 c : ℚ) / 1000000000000

private def jointExponent_s14_r1 (c : MME.ReleasedInterior.Split 14) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 3 14).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s14_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 14 => c.val 0)
        (fun c => (splitWeight 3 14 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 14 => (splitWeight 3 14 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 14) : 0 ≤ alphaQ_s14_r1 c := by
    unfold alphaQ_s14_r1
    positivity
  have hprob : ∑ c, alphaQ_s14_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000006597,499999993403,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,7032701133,492967342574,492967124858,7032831435] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 14 2 c : ℚ) / 1000000000000

private def jointExponent_s14_r2 (c : MME.ReleasedInterior.Split 14) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 3 14).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s14_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 14 => c.val 0)
        (fun c => (splitWeight 3 14 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 14 => (splitWeight 3 14 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 14) : 0 ≤ alphaQ_s14_r2 c := by
    unfold alphaQ_s14_r2
    positivity
  have hprob : ∑ c, alphaQ_s14_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000007947,499999992053,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,7067619706,492932428896,492932203966,7067747432] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 14 3 c : ℚ) / 1000000000000

private def jointExponent_s14_r3 (c : MME.ReleasedInterior.Split 14) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 3 14).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s14_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 14 => c.val 0)
        (fun c => (splitWeight 3 14 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 14 => (splitWeight 3 14 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 14) : 0 ≤ alphaQ_s14_r3 c := by
    unfold alphaQ_s14_r3
    positivity
  have hprob : ∑ c, alphaQ_s14_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999996329,500000003671,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,7170883605,492829207273,492828877265,7171031857] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s14_r5 (c : MME.ReleasedInterior.Split 14) : ℚ :=
  (splitWeight 3 14 5 c : ℚ) / 1000000000000

private def jointExponent_s14_r5 (c : MME.ReleasedInterior.Split 14) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 3 14).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s14_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 14 => c.val 0)
        (fun c => (splitWeight 3 14 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 14 => (splitWeight 3 14 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 14) : 0 ≤ alphaQ_s14_r5 c := by
    unfold alphaQ_s14_r5
    positivity
  have hprob : ∑ c, alphaQ_s14_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999948336,500000051664,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,7152360018,492847703097,492847826426,7152110459] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 15 0 c : ℚ) / 1000000000000

private def jointExponent_s15_r0 (c : MME.ReleasedInterior.Split 15) : ℕ :=
  [3, 1, 1, 3].getD ((seed 3 15).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s15_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 15 => c.val 0)
        (fun c => (splitWeight 3 15 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 15 => (splitWeight 3 15 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 15) : 0 ≤ alphaQ_s15_r0 c := by
    unfold alphaQ_s15_r0
    positivity
  have hprob : ∑ c, alphaQ_s15_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000308167,499999691833,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500002325984,499997674016,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 15 1 c : ℚ) / 1000000000000

private def jointExponent_s15_r1 (c : MME.ReleasedInterior.Split 15) : ℕ :=
  [3, 1, 1, 3].getD ((seed 3 15).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s15_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 15 => c.val 0)
        (fun c => (splitWeight 3 15 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 15 => (splitWeight 3 15 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 15) : 0 ≤ alphaQ_s15_r1 c := by
    unfold alphaQ_s15_r1
    positivity
  have hprob : ∑ c, alphaQ_s15_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499853598316,500146401684,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500283777931,499716222069,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 15 2 c : ℚ) / 1000000000000

private def jointExponent_s15_r2 (c : MME.ReleasedInterior.Split 15) : ℕ :=
  [3, 1, 1, 3].getD ((seed 3 15).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s15_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 15 => c.val 0)
        (fun c => (splitWeight 3 15 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 15 => (splitWeight 3 15 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 15) : 0 ≤ alphaQ_s15_r2 c := by
    unfold alphaQ_s15_r2
    positivity
  have hprob : ∑ c, alphaQ_s15_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499887308688,500112691312,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500219293267,499780706733,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 15 3 c : ℚ) / 1000000000000

private def jointExponent_s15_r3 (c : MME.ReleasedInterior.Split 15) : ℕ :=
  [3, 1, 1, 3].getD ((seed 3 15).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s15_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 15 => c.val 0)
        (fun c => (splitWeight 3 15 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 15 => (splitWeight 3 15 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 15) : 0 ≤ alphaQ_s15_r3 c := by
    unfold alphaQ_s15_r3
    positivity
  have hprob : ∑ c, alphaQ_s15_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499927558678,500072441322,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500140555276,499859444724,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 15 4 c : ℚ) / 1000000000000

private def jointExponent_s15_r4 (c : MME.ReleasedInterior.Split 15) : ℕ :=
  [3, 1, 1, 3].getD ((seed 3 15).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s15_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 15 => c.val 0)
        (fun c => (splitWeight 3 15 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 15 => (splitWeight 3 15 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 15) : 0 ≤ alphaQ_s15_r4 c := by
    unfold alphaQ_s15_r4
    positivity
  have hprob : ∑ c, alphaQ_s15_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000305789,499999694211,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500002251367,499997748633,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 15 5 c : ℚ) / 1000000000000

private def jointExponent_s15_r5 (c : MME.ReleasedInterior.Split 15) : ℕ :=
  [3, 1, 1, 3].getD ((seed 3 15).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s15_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 15 => c.val 0)
        (fun c => (splitWeight 3 15 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 15 => (splitWeight 3 15 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 15) : 0 ≤ alphaQ_s15_r5 c := by
    unfold alphaQ_s15_r5
    positivity
  have hprob : ∑ c, alphaQ_s15_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000314327,499999685673,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500002235127,499997764873,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s18_r2 (c : MME.ReleasedInterior.Split 18) : ℚ :=
  (splitWeight 3 18 2 c : ℚ) / 1000000000000

private def jointExponent_s18_r2 (c : MME.ReleasedInterior.Split 18) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 3 18).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s18_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 18 => c.val 0)
        (fun c => (splitWeight 3 18 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 18 => (splitWeight 3 18 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 18) : 0 ≤ alphaQ_s18_r2 c := by
    unfold alphaQ_s18_r2
    positivity
  have hprob : ∑ c, alphaQ_s18_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999905448,500000094552,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,6634845811,493365063607,493365713778,6634376804] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s18_r3 (c : MME.ReleasedInterior.Split 18) : ℚ :=
  (splitWeight 3 18 3 c : ℚ) / 1000000000000

private def jointExponent_s18_r3 (c : MME.ReleasedInterior.Split 18) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 3 18).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s18_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 18 => c.val 0)
        (fun c => (splitWeight 3 18 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 18 => (splitWeight 3 18 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 18) : 0 ≤ alphaQ_s18_r3 c := by
    unfold alphaQ_s18_r3
    positivity
  have hprob : ∑ c, alphaQ_s18_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999982914,500000017086,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,6611577300,493388411800,493388485535,6611525365] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s18_r5 (c : MME.ReleasedInterior.Split 18) : ℚ :=
  (splitWeight 3 18 5 c : ℚ) / 1000000000000

private def jointExponent_s18_r5 (c : MME.ReleasedInterior.Split 18) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 3 18).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s18_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 18 => c.val 0)
        (fun c => (splitWeight 3 18 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 18 => (splitWeight 3 18 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 18) : 0 ≤ alphaQ_s18_r5 c := by
    unfold alphaQ_s18_r5
    positivity
  have hprob : ∑ c, alphaQ_s18_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999978439,500000021561,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,6587213728,493412741888,493412983517,6587060867] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 19 2 c : ℚ) / 1000000000000

private def jointExponent_s19_r2 (c : MME.ReleasedInterior.Split 19) : ℕ :=
  [12, 5, 5, 3, 1, 3, 5, 5, 12].getD ((seed 3 19).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s19_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 19 => c.val 0)
        (fun c => (splitWeight 3 19 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 19 => (splitWeight 3 19 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 19) : 0 ≤ alphaQ_s19_r2 c := by
    unfold alphaQ_s19_r2
    positivity
  have hprob : ∑ c, alphaQ_s19_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![180482819310,639034371429,180482809261,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![318907888,71763104294,855835968361,71763099041,318920416] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s19_r2 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![3,1,3,0,0] ![3,1,3,40,40] ![12,4,0,4,12] jointExponent_s19_r2 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 19 => c.val 0)
        (fun c => (alphaQ_s19_r2 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s19_r2 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s19_r2, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s19_r3 (c : MME.ReleasedInterior.Split 19) : ℚ :=
  (splitWeight 3 19 3 c : ℚ) / 1000000000000

private def jointExponent_s19_r3 (c : MME.ReleasedInterior.Split 19) : ℕ :=
  [12, 5, 5, 3, 1, 3, 5, 5, 12].getD ((seed 3 19).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s19_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 19 => c.val 0)
        (fun c => (splitWeight 3 19 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 19 => (splitWeight 3 19 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 19) : 0 ≤ alphaQ_s19_r3 c := by
    unfold alphaQ_s19_r3
    positivity
  have hprob : ∑ c, alphaQ_s19_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![183320041036,633359952500,183320006464,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![320799892,72974655513,853409090729,72974583472,320870394] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s19_r3 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![3,1,3,0,0] ![3,1,3,40,40] ![12,4,0,4,12] jointExponent_s19_r3 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 19 => c.val 0)
        (fun c => (alphaQ_s19_r3 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s19_r3 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s19_r3, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s19_r4 (c : MME.ReleasedInterior.Split 19) : ℚ :=
  (splitWeight 3 19 4 c : ℚ) / 1000000000000

private def jointExponent_s19_r4 (c : MME.ReleasedInterior.Split 19) : ℕ :=
  [12, 5, 5, 3, 1, 3, 5, 5, 12].getD ((seed 3 19).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s19_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 19 => c.val 0)
        (fun c => (splitWeight 3 19 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 19 => (splitWeight 3 19 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 19) : 0 ≤ alphaQ_s19_r4 c := by
    unfold alphaQ_s19_r4
    positivity
  have hprob : ∑ c, alphaQ_s19_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![180454082338,639091843667,180454073995,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![318782787,71756383363,855849672806,71756345914,318815130] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 19 5 c : ℚ) / 1000000000000

private def jointExponent_s19_r5 (c : MME.ReleasedInterior.Split 19) : ℕ :=
  [12, 5, 5, 3, 1, 3, 5, 5, 12].getD ((seed 3 19).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s19_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 19 => c.val 0)
        (fun c => (splitWeight 3 19 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 19 => (splitWeight 3 19 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 19) : 0 ≤ alphaQ_s19_r5 c := by
    unfold alphaQ_s19_r5
    positivity
  have hprob : ∑ c, alphaQ_s19_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![183347838628,633304357408,183347803964,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![319650927,72973005962,853414689909,72972930050,319723152] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s20_r0 (c : MME.ReleasedInterior.Split 20) : ℚ :=
  (splitWeight 3 20 0 c : ℚ) / 1000000000000

private def jointExponent_s20_r0 (c : MME.ReleasedInterior.Split 20) : ℕ :=
  [9, 7, 6, 2, 3, 3, 2, 6, 7, 9].getD ((seed 3 20).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s20_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 20 => c.val 0)
        (fun c => (splitWeight 3 20 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 20 => (splitWeight 3 20 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 20) : 0 ≤ alphaQ_s20_r0 c := by
    unfold alphaQ_s20_r0
    positivity
  have hprob : ∑ c, alphaQ_s20_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![13654244424,486345750548,486345762874,13654242154,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![12670397855,487329600251,487329621345,12670380549,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 20 1 c : ℚ) / 1000000000000

private def jointExponent_s20_r1 (c : MME.ReleasedInterior.Split 20) : ℕ :=
  [9, 7, 7, 2, 3, 3, 2, 7, 7, 9].getD ((seed 3 20).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s20_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 20 => c.val 0)
        (fun c => (splitWeight 3 20 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 20 => (splitWeight 3 20 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 20) : 0 ≤ alphaQ_s20_r1 c := by
    unfold alphaQ_s20_r1
    positivity
  have hprob : ∑ c, alphaQ_s20_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![13040042970,486959952507,486959951620,13040052903,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![12230795996,487769202451,487769229737,12230771816,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s20_r4 (c : MME.ReleasedInterior.Split 20) : ℚ :=
  (splitWeight 3 20 4 c : ℚ) / 1000000000000

private def jointExponent_s20_r4 (c : MME.ReleasedInterior.Split 20) : ℕ :=
  [9, 7, 7, 2, 3, 3, 2, 7, 7, 9].getD ((seed 3 20).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s20_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 20 => c.val 0)
        (fun c => (splitWeight 3 20 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 20 => (splitWeight 3 20 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 20) : 0 ≤ alphaQ_s20_r4 c := by
    unfold alphaQ_s20_r4
    positivity
  have hprob : ∑ c, alphaQ_s20_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![12288013201,487711984267,487711984918,12288017614,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![12957311601,487042686368,487042703725,12957298306,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 20 5 c : ℚ) / 1000000000000

private def jointExponent_s20_r5 (c : MME.ReleasedInterior.Split 20) : ℕ :=
  [9, 6, 7, 2, 3, 3, 2, 7, 6, 9].getD ((seed 3 20).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s20_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 20 => c.val 0)
        (fun c => (splitWeight 3 20 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 20 => (splitWeight 3 20 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 20) : 0 ≤ alphaQ_s20_r5 c := by
    unfold alphaQ_s20_r5
    positivity
  have hprob : ∑ c, alphaQ_s20_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![12738672651,487261322442,487261320239,12738684668,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![13573492542,486426508090,486426527003,13573472365,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 21 0 c : ℚ) / 1000000000000

private def jointExponent_s21_r0 (c : MME.ReleasedInterior.Split 21) : ℕ :=
  [12, 5, 3, 5, 1, 5, 3, 5, 12].getD ((seed 3 21).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s21_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 21 => c.val 0)
        (fun c => (splitWeight 3 21 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 21 => (splitWeight 3 21 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 21) : 0 ≤ alphaQ_s21_r0 c := by
    unfold alphaQ_s21_r0
    positivity
  have hprob : ∑ c, alphaQ_s21_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![333432417,77543043035,844247053947,77543041231,333429370] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![183438370382,633123240945,183438388673,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 21 1 c : ℚ) / 1000000000000

private def jointExponent_s21_r1 (c : MME.ReleasedInterior.Split 21) : ℕ :=
  [12, 5, 3, 5, 1, 5, 3, 5, 12].getD ((seed 3 21).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s21_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 21 => c.val 0)
        (fun c => (splitWeight 3 21 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 21 => (splitWeight 3 21 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 21) : 0 ≤ alphaQ_s21_r1 c := by
    unfold alphaQ_s21_r1
    positivity
  have hprob : ∑ c, alphaQ_s21_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![328708898,76179315418,846983956798,76179308542,328710344] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![180570853886,638858275790,180570870324,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 21 2 c : ℚ) / 1000000000000

private def jointExponent_s21_r2 (c : MME.ReleasedInterior.Split 21) : ℕ :=
  [12, 5, 3, 5, 1, 5, 3, 5, 12].getD ((seed 3 21).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s21_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 21 => c.val 0)
        (fun c => (splitWeight 3 21 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 21 => (splitWeight 3 21 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 21) : 0 ≤ alphaQ_s21_r2 c := by
    unfold alphaQ_s21_r2
    positivity
  have hprob : ∑ c, alphaQ_s21_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![183364510613,633270990498,183364498889,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![333424600,77543395129,844246365056,77543391087,333424128] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 21 3 c : ℚ) / 1000000000000

private def jointExponent_s21_r3 (c : MME.ReleasedInterior.Split 21) : ℕ :=
  [12, 5, 3, 5, 1, 5, 3, 5, 12].getD ((seed 3 21).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s21_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 21 => c.val 0)
        (fun c => (splitWeight 3 21 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 21 => (splitWeight 3 21 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 21) : 0 ≤ alphaQ_s21_r3 c := by
    unfold alphaQ_s21_r3
    positivity
  have hprob : ∑ c, alphaQ_s21_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![180514718865,638970571762,180514709373,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![328723242,76183782754,846974991006,76183782029,328720969] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 21 4 c : ℚ) / 1000000000000

private def jointExponent_s21_r4 (c : MME.ReleasedInterior.Split 21) : ℕ :=
  [12, 5, 3, 5, 1, 5, 3, 5, 12].getD ((seed 3 21).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s21_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 21 => c.val 0)
        (fun c => (splitWeight 3 21 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 21 => (splitWeight 3 21 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 21) : 0 ≤ alphaQ_s21_r4 c := by
    unfold alphaQ_s21_r4
    positivity
  have hprob : ∑ c, alphaQ_s21_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![328747175,76797778150,845746954199,76797773174,328747302] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![181705309050,636589365860,181705325090,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 21 5 c : ℚ) / 1000000000000

private def jointExponent_s21_r5 (c : MME.ReleasedInterior.Split 21) : ℕ :=
  [12, 5, 3, 5, 1, 5, 3, 5, 12].getD ((seed 3 21).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s21_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 21 => c.val 0)
        (fun c => (splitWeight 3 21 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 21 => (splitWeight 3 21 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 21) : 0 ≤ alphaQ_s21_r5 c := by
    unfold alphaQ_s21_r5
    positivity
  have hprob : ∑ c, alphaQ_s21_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![181628254171,636743511054,181628234775,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![328736653,76801419447,845739693336,76801400043,328750521] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 22 0 c : ℚ) / 1000000000000

private def jointExponent_s22_r0 (c : MME.ReleasedInterior.Split 22) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 3 22).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s22_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 22 => c.val 0)
        (fun c => (splitWeight 3 22 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 22 => (splitWeight 3 22 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 22) : 0 ≤ alphaQ_s22_r0 c := by
    unfold alphaQ_s22_r0
    positivity
  have hprob : ∑ c, alphaQ_s22_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7069534803,492930482690,492930462069,7069520438] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999979304,500000020696,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 22 1 c : ℚ) / 1000000000000

private def jointExponent_s22_r1 (c : MME.ReleasedInterior.Split 22) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 3 22).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s22_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 22 => c.val 0)
        (fun c => (splitWeight 3 22 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 22 => (splitWeight 3 22 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 22) : 0 ≤ alphaQ_s22_r1 c := by
    unfold alphaQ_s22_r1
    positivity
  have hprob : ∑ c, alphaQ_s22_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7184074815,492815821702,492815940823,7184162660] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000104993,499999895007,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 22 2 c : ℚ) / 1000000000000

private def jointExponent_s22_r2 (c : MME.ReleasedInterior.Split 22) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 3 22).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s22_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 22 => c.val 0)
        (fun c => (splitWeight 3 22 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 22 => (splitWeight 3 22 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 22) : 0 ≤ alphaQ_s22_r2 c := by
    unfold alphaQ_s22_r2
    positivity
  have hprob : ∑ c, alphaQ_s22_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7070883387,492929133063,492929084733,7070898817] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999981157,500000018843,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 22 3 c : ℚ) / 1000000000000

private def jointExponent_s22_r3 (c : MME.ReleasedInterior.Split 22) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 3 22).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s22_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 22 => c.val 0)
        (fun c => (splitWeight 3 22 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 22 => (splitWeight 3 22 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 22) : 0 ≤ alphaQ_s22_r3 c := by
    unfold alphaQ_s22_r3
    positivity
  have hprob : ∑ c, alphaQ_s22_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7036072526,492963965107,492963898408,7036063959] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999963454,500000036546,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 22 4 c : ℚ) / 1000000000000

private def jointExponent_s22_r4 (c : MME.ReleasedInterior.Split 22) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 3 22).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s22_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 22 => c.val 0)
        (fun c => (splitWeight 3 22 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 22 => (splitWeight 3 22 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 22) : 0 ≤ alphaQ_s22_r4 c := by
    unfold alphaQ_s22_r4
    positivity
  have hprob : ∑ c, alphaQ_s22_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7155215530,492844912060,492844661887,7155210523] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999865922,500000134078,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s25_r2 (c : MME.ReleasedInterior.Split 25) : ℚ :=
  (splitWeight 3 25 2 c : ℚ) / 1000000000000

private def jointExponent_s25_r2 (c : MME.ReleasedInterior.Split 25) : ℕ :=
  [12, 4, 6, 1, 1, 6, 4, 12].getD ((seed 3 25).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s25_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 25 => c.val 0)
        (fun c => (splitWeight 3 25 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 25 => (splitWeight 3 25 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 25) : 0 ≤ alphaQ_s25_r2 c := by
    unfold alphaQ_s25_r2
    positivity
  have hprob : ∑ c, alphaQ_s25_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999993048,500000006952,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![328211022,70622506631,858098560700,70622515655,328205992] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s25_r3 (c : MME.ReleasedInterior.Split 25) : ℚ :=
  (splitWeight 3 25 3 c : ℚ) / 1000000000000

private def jointExponent_s25_r3 (c : MME.ReleasedInterior.Split 25) : ℕ :=
  [12, 4, 6, 1, 1, 6, 4, 12].getD ((seed 3 25).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s25_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 25 => c.val 0)
        (fun c => (splitWeight 3 25 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 25 => (splitWeight 3 25 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 25) : 0 ≤ alphaQ_s25_r3 c := by
    unfold alphaQ_s25_r3
    positivity
  have hprob : ∑ c, alphaQ_s25_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000022929,499999977071,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![325072072,73633315923,852083237820,73633302881,325071304] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s25_r5 (c : MME.ReleasedInterior.Split 25) : ℚ :=
  (splitWeight 3 25 5 c : ℚ) / 1000000000000

private def jointExponent_s25_r5 (c : MME.ReleasedInterior.Split 25) : ℕ :=
  [12, 4, 6, 1, 1, 6, 4, 12].getD ((seed 3 25).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s25_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 25 => c.val 0)
        (fun c => (splitWeight 3 25 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 25 => (splitWeight 3 25 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 25) : 0 ≤ alphaQ_s25_r5 c := by
    unfold alphaQ_s25_r5
    positivity
  have hprob : ∑ c, alphaQ_s25_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000016851,499999983149,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![328173529,73610333217,852122990520,73610327779,328174955] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 26 0 c : ℚ) / 1000000000000

private def jointExponent_s26_r0 (c : MME.ReleasedInterior.Split 26) : ℕ :=
  [7, 9, 3, 2, 7, 7, 2, 3, 9, 7].getD ((seed 3 26).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s26_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 26 => c.val 0)
        (fun c => (splitWeight 3 26 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 26 => (splitWeight 3 26 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 26) : 0 ≤ alphaQ_s26_r0 c := by
    unfold alphaQ_s26_r0
    positivity
  have hprob : ∑ c, alphaQ_s26_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![13162331431,486837656004,486837596562,13162416003,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![12248430087,487751586097,487751635927,12248347889,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 26 1 c : ℚ) / 1000000000000

private def jointExponent_s26_r1 (c : MME.ReleasedInterior.Split 26) : ℕ :=
  [7, 9, 3, 2, 6, 6, 2, 3, 9, 7].getD ((seed 3 26).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s26_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 26 => c.val 0)
        (fun c => (splitWeight 3 26 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 26 => (splitWeight 3 26 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 26) : 0 ≤ alphaQ_s26_r1 c := by
    unfold alphaQ_s26_r1
    positivity
  have hprob : ∑ c, alphaQ_s26_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![13771902830,486228076594,486227993078,13772027498,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![12681352451,487318673242,487318746690,12681227617,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 26 2 c : ℚ) / 1000000000000

private def jointExponent_s26_r2 (c : MME.ReleasedInterior.Split 26) : ℕ :=
  [7, 9, 3, 2, 7, 7, 2, 3, 9, 7].getD ((seed 3 26).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s26_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 26 => c.val 0)
        (fun c => (splitWeight 3 26 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 26 => (splitWeight 3 26 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 26) : 0 ≤ alphaQ_s26_r2 c := by
    unfold alphaQ_s26_r2
    positivity
  have hprob : ∑ c, alphaQ_s26_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![12391042721,487608957904,487608978989,12391020386,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![12955693084,487044302616,487044292646,12955711654,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 26 3 c : ℚ) / 1000000000000

private def jointExponent_s26_r3 (c : MME.ReleasedInterior.Split 26) : ℕ :=
  [6, 9, 3, 2, 7, 7, 2, 3, 9, 6].getD ((seed 3 26).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s26_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 26 => c.val 0)
        (fun c => (splitWeight 3 26 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 26 => (splitWeight 3 26 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 26) : 0 ≤ alphaQ_s26_r3 c := by
    unfold alphaQ_s26_r3
    positivity
  have hprob : ∑ c, alphaQ_s26_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![12848643942,487151355255,487151360102,12848640701,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![13576412854,486423586134,486423588881,13576412131,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s27_r2 (c : MME.ReleasedInterior.Split 27) : ℚ :=
  (splitWeight 3 27 2 c : ℚ) / 1000000000000

private def jointExponent_s27_r2 (c : MME.ReleasedInterior.Split 27) : ℕ :=
  [6, 3, 7, 9, 2, 2, 9, 7, 3, 6].getD ((seed 3 27).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s27_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 27 => c.val 0)
        (fun c => (splitWeight 3 27 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 27 => (splitWeight 3 27 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 27) : 0 ≤ alphaQ_s27_r2 c := by
    unfold alphaQ_s27_r2
    positivity
  have hprob : ∑ c, alphaQ_s27_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![12849937155,487149965284,487149598837,12850498724,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![13662450488,486337643612,486338001973,13661903927,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 27 3 c : ℚ) / 1000000000000

private def jointExponent_s27_r3 (c : MME.ReleasedInterior.Split 27) : ℕ :=
  [7, 3, 7, 9, 2, 2, 9, 7, 3, 7].getD ((seed 3 27).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s27_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 27 => c.val 0)
        (fun c => (splitWeight 3 27 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 27 => (splitWeight 3 27 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 27) : 0 ≤ alphaQ_s27_r3 c := by
    unfold alphaQ_s27_r3
    positivity
  have hprob : ∑ c, alphaQ_s27_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![12399072572,487600844058,487600423379,12399659991,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![13040414882,486959682124,486960070681,13039832313,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 27 4 c : ℚ) / 1000000000000

private def jointExponent_s27_r4 (c : MME.ReleasedInterior.Split 27) : ℕ :=
  [7, 3, 6, 9, 2, 2, 9, 6, 3, 7].getD ((seed 3 27).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s27_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 27 => c.val 0)
        (fun c => (splitWeight 3 27 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 27 => (splitWeight 3 27 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 27) : 0 ≤ alphaQ_s27_r4 c := by
    unfold alphaQ_s27_r4
    positivity
  have hprob : ∑ c, alphaQ_s27_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![13775667550,486224311484,486224202070,13775818896,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![12749619837,487250415338,487250520145,12749444680,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 27 5 c : ℚ) / 1000000000000

private def jointExponent_s27_r5 (c : MME.ReleasedInterior.Split 27) : ℕ :=
  [7, 3, 7, 9, 2, 2, 9, 7, 3, 7].getD ((seed 3 27).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s27_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 27 => c.val 0)
        (fun c => (splitWeight 3 27 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 27 => (splitWeight 3 27 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 27) : 0 ≤ alphaQ_s27_r5 c := by
    unfold alphaQ_s27_r5
    positivity
  have hprob : ∑ c, alphaQ_s27_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![13161935431,486838045404,486837936717,13162082448,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![12313450053,487686576881,487686690720,12313282346,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 28 0 c : ℚ) / 1000000000000

private def jointExponent_s28_r0 (c : MME.ReleasedInterior.Split 28) : ℕ :=
  [12, 4, 1, 6, 6, 1, 4, 12].getD ((seed 3 28).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s28_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 28 => c.val 0)
        (fun c => (splitWeight 3 28 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 28 => (splitWeight 3 28 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 28) : 0 ≤ alphaQ_s28_r0 c := by
    unfold alphaQ_s28_r0
    positivity
  have hprob : ∑ c, alphaQ_s28_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![330509153,77756300765,843826388694,77756292865,330508523] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000016434,499999983566,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s28_r2 (c : MME.ReleasedInterior.Split 28) : ℚ :=
  (splitWeight 3 28 2 c : ℚ) / 1000000000000

private def jointExponent_s28_r2 (c : MME.ReleasedInterior.Split 28) : ℕ :=
  [12, 4, 1, 6, 6, 1, 4, 12].getD ((seed 3 28).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s28_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 28 => c.val 0)
        (fun c => (splitWeight 3 28 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 28 => (splitWeight 3 28 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 28) : 0 ≤ alphaQ_s28_r2 c := by
    unfold alphaQ_s28_r2
    positivity
  have hprob : ∑ c, alphaQ_s28_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![328495507,77721942355,843899109524,77721948796,328503818] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999975870,500000024130,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s28_r3 (c : MME.ReleasedInterior.Split 28) : ℚ :=
  (splitWeight 3 28 3 c : ℚ) / 1000000000000

private def jointExponent_s28_r3 (c : MME.ReleasedInterior.Split 28) : ℕ :=
  [12, 4, 1, 6, 6, 1, 4, 12].getD ((seed 3 28).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s28_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 28 => c.val 0)
        (fun c => (splitWeight 3 28 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 28 => (splitWeight 3 28 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 28) : 0 ≤ alphaQ_s28_r3 c := by
    unfold alphaQ_s28_r3
    positivity
  have hprob : ∑ c, alphaQ_s28_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![328230826,74879431640,849584672857,74879428856,328235821] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999999795,500000000205,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s28_r3 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![6,1,1,6,0] ![12,4,0,4,12] ![1,1,40,40,40] jointExponent_s28_r3 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 28 => c.val 0)
        (fun c => (alphaQ_s28_r3 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s28_r3 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s28_r3, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s31_r0 (c : MME.ReleasedInterior.Split 31) : ℚ :=
  (splitWeight 3 31 0 c : ℚ) / 1000000000000

private def jointExponent_s31_r0 (c : MME.ReleasedInterior.Split 31) : ℕ :=
  [6, 12, 1, 4, 4, 1, 12, 6].getD ((seed 3 31).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s31_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 31 => c.val 0)
        (fun c => (splitWeight 3 31 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 31 => (splitWeight 3 31 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 31) : 0 ≤ alphaQ_s31_r0 c := by
    unfold alphaQ_s31_r0
    positivity
  have hprob : ∑ c, alphaQ_s31_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![324717744,77737758950,843875042137,77737760951,324720218] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999993277,500000006723,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 31 1 c : ℚ) / 1000000000000

private def jointExponent_s31_r1 (c : MME.ReleasedInterior.Split 31) : ℕ :=
  [6, 12, 1, 4, 4, 1, 12, 6].getD ((seed 3 31).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s31_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 31 => c.val 0)
        (fun c => (splitWeight 3 31 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 31 => (splitWeight 3 31 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 31) : 0 ≤ alphaQ_s31_r1 c := by
    unfold alphaQ_s31_r1
    positivity
  have hprob : ∑ c, alphaQ_s31_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![327499294,80462253951,838420479136,80462263791,327503828] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999976871,500000023129,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s31_r4 (c : MME.ReleasedInterior.Split 31) : ℚ :=
  (splitWeight 3 31 4 c : ℚ) / 1000000000000

private def jointExponent_s31_r4 (c : MME.ReleasedInterior.Split 31) : ℕ :=
  [6, 12, 1, 4, 4, 1, 12, 6].getD ((seed 3 31).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s31_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 31 => c.val 0)
        (fun c => (splitWeight 3 31 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 31 => (splitWeight 3 31 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 31) : 0 ≤ alphaQ_s31_r4 c := by
    unfold alphaQ_s31_r4
    positivity
  have hprob : ∑ c, alphaQ_s31_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![328677997,80534811864,838273023682,80534810125,328676332] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000005914,499999994086,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s32_r0 (c : MME.ReleasedInterior.Split 32) : ℚ :=
  (splitWeight 3 32 0 c : ℚ) / 1000000000000

private def jointExponent_s32_r0 (c : MME.ReleasedInterior.Split 32) : ℕ :=
  [3, 5, 12, 5, 1, 5, 12, 5, 3].getD ((seed 3 32).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s32_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 32 => c.val 0)
        (fun c => (splitWeight 3 32 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 32 => (splitWeight 3 32 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 32) : 0 ≤ alphaQ_s32_r0 c := by
    unfold alphaQ_s32_r0
    positivity
  have hprob : ∑ c, alphaQ_s32_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![335753092,79186075811,840956346288,79186055587,335769222] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![180629780238,638740431413,180629788349,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s32_r2 (c : MME.ReleasedInterior.Split 32) : ℚ :=
  (splitWeight 3 32 2 c : ℚ) / 1000000000000

private def jointExponent_s32_r2 (c : MME.ReleasedInterior.Split 32) : ℕ :=
  [3, 5, 12, 5, 1, 5, 12, 5, 3].getD ((seed 3 32).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s32_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 32 => c.val 0)
        (fun c => (splitWeight 3 32 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 32 => (splitWeight 3 32 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 32) : 0 ≤ alphaQ_s32_r2 c := by
    unfold alphaQ_s32_r2
    positivity
  have hprob : ∑ c, alphaQ_s32_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![335954784,79859110825,839609875420,79859158060,335900911] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![181883563693,636232827833,181883608474,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s32_r3 (c : MME.ReleasedInterior.Split 32) : ℚ :=
  (splitWeight 3 32 3 c : ℚ) / 1000000000000

private def jointExponent_s32_r3 (c : MME.ReleasedInterior.Split 32) : ℕ :=
  [3, 5, 12, 5, 1, 5, 12, 5, 3].getD ((seed 3 32).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s32_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 32 => c.val 0)
        (fun c => (splitWeight 3 32 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 32 => (splitWeight 3 32 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 32) : 0 ≤ alphaQ_s32_r3 c := by
    unfold alphaQ_s32_r3
    positivity
  have hprob : ∑ c, alphaQ_s32_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![335893816,79860422832,839607372463,79860464155,335846734] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![181832566875,636334854725,181832578400,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s32_r5 (c : MME.ReleasedInterior.Split 32) : ℚ :=
  (splitWeight 3 32 5 c : ℚ) / 1000000000000

private def jointExponent_s32_r5 (c : MME.ReleasedInterior.Split 32) : ℕ :=
  [3, 5, 12, 5, 1, 5, 12, 5, 3].getD ((seed 3 32).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s32_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 32 => c.val 0)
        (fun c => (splitWeight 3 32 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 32 => (splitWeight 3 32 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 32) : 0 ≤ alphaQ_s32_r5 c := by
    unfold alphaQ_s32_r5
    positivity
  have hprob : ∑ c, alphaQ_s32_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![335704426,79186225320,840956149007,79186203479,335717768] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![180577446461,638845121360,180577432179,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s33_r1 (c : MME.ReleasedInterior.Split 33) : ℚ :=
  (splitWeight 3 33 1 c : ℚ) / 1000000000000

private def jointExponent_s33_r1 (c : MME.ReleasedInterior.Split 33) : ℕ :=
  [6, 1, 4, 12, 12, 4, 1, 6].getD ((seed 3 33).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s33_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 33 => c.val 0)
        (fun c => (splitWeight 3 33 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 33 => (splitWeight 3 33 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 33) : 0 ≤ alphaQ_s33_r1 c := by
    unfold alphaQ_s33_r1
    positivity
  have hprob : ∑ c, alphaQ_s33_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![330159803,80553592868,838232403256,80553646554,330197519] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999856296,500000143704,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s33_r1 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![12,4,0,4,12] ![12,4,0,4,12] ![1,1,40,40,40] jointExponent_s33_r1 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 33 => c.val 0)
        (fun c => (alphaQ_s33_r1 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s33_r1 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s33_r1, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s33_r4 (c : MME.ReleasedInterior.Split 33) : ℚ :=
  (splitWeight 3 33 4 c : ℚ) / 1000000000000

private def jointExponent_s33_r4 (c : MME.ReleasedInterior.Split 33) : ℕ :=
  [6, 1, 4, 12, 12, 4, 1, 6].getD ((seed 3 33).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s33_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 33 => c.val 0)
        (fun c => (splitWeight 3 33 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 33 => (splitWeight 3 33 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 33) : 0 ≤ alphaQ_s33_r4 c := by
    unfold alphaQ_s33_r4
    positivity
  have hprob : ∑ c, alphaQ_s33_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![328820192,80478232201,838385937344,80478231963,328778300] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000053082,499999946918,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 33 5 c : ℚ) / 1000000000000

private def jointExponent_s33_r5 (c : MME.ReleasedInterior.Split 33) : ℕ :=
  [6, 1, 4, 12, 12, 4, 1, 6].getD ((seed 3 33).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s33_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 33 => c.val 0)
        (fun c => (splitWeight 3 33 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 33 => (splitWeight 3 33 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 33) : 0 ≤ alphaQ_s33_r5 c := by
    unfold alphaQ_s33_r5
    positivity
  have hprob : ∑ c, alphaQ_s33_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![326459123,77742294982,843862525518,77742324163,326396214] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000013784,499999986216,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 36 0 c : ℚ) / 1000000000000

private def jointExponent_s36_r0 (c : MME.ReleasedInterior.Split 36) : ℕ :=
  [3, 7, 2, 2, 7, 3].getD ((seed 3 36).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s36_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 36 => c.val 0)
        (fun c => (splitWeight 3 36 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 36 => (splitWeight 3 36 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 36) : 0 ≤ alphaQ_s36_r0 c := by
    unfold alphaQ_s36_r0
    positivity
  have hprob : ∑ c, alphaQ_s36_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7257056343,492742981908,492742663002,7257298747] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000061329,499999938671,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 36 1 c : ℚ) / 1000000000000

private def jointExponent_s36_r1 (c : MME.ReleasedInterior.Split 36) : ℕ :=
  [3, 7, 2, 2, 7, 3].getD ((seed 3 36).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s36_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 36 => c.val 0)
        (fun c => (splitWeight 3 36 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 36 => (splitWeight 3 36 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 36) : 0 ≤ alphaQ_s36_r1 c := by
    unfold alphaQ_s36_r1
    positivity
  have hprob : ∑ c, alphaQ_s36_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7352143588,492648172664,492642901448,7356782300] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500001444979,499998555021,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s36_r3 (c : MME.ReleasedInterior.Split 36) : ℚ :=
  (splitWeight 3 36 3 c : ℚ) / 1000000000000

private def jointExponent_s36_r3 (c : MME.ReleasedInterior.Split 36) : ℕ :=
  [3, 7, 2, 2, 7, 3].getD ((seed 3 36).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s36_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 36 => c.val 0)
        (fun c => (splitWeight 3 36 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 36 => (splitWeight 3 36 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 36) : 0 ≤ alphaQ_s36_r3 c := by
    unfold alphaQ_s36_r3
    positivity
  have hprob : ∑ c, alphaQ_s36_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7316516622,492683470357,492683527517,7316485504] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000034667,499999965333,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 36 4 c : ℚ) / 1000000000000

private def jointExponent_s36_r4 (c : MME.ReleasedInterior.Split 36) : ℕ :=
  [3, 7, 2, 2, 7, 3].getD ((seed 3 36).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s36_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 36 => c.val 0)
        (fun c => (splitWeight 3 36 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 36 => (splitWeight 3 36 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 36) : 0 ≤ alphaQ_s36_r4 c := by
    unfold alphaQ_s36_r4
    positivity
  have hprob : ∑ c, alphaQ_s36_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7368638713,492631701986,492628165975,7371493326] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000723756,499999276244,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 36 5 c : ℚ) / 1000000000000

private def jointExponent_s36_r5 (c : MME.ReleasedInterior.Split 36) : ℕ :=
  [3, 7, 2, 2, 7, 3].getD ((seed 3 36).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s36_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 36 => c.val 0)
        (fun c => (splitWeight 3 36 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 36 => (splitWeight 3 36 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 36) : 0 ≤ alphaQ_s36_r5 c := by
    unfold alphaQ_s36_r5
    positivity
  have hprob : ∑ c, alphaQ_s36_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7328866201,492671097418,492671523184,7328513197] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999937169,500000062831,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 37 0 c : ℚ) / 1000000000000

private def jointExponent_s37_r0 (c : MME.ReleasedInterior.Split 37) : ℕ :=
  [3, 2, 7, 7, 2, 3].getD ((seed 3 37).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s37_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 37 => c.val 0)
        (fun c => (splitWeight 3 37 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 37 => (splitWeight 3 37 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 37) : 0 ≤ alphaQ_s37_r0 c := by
    unfold alphaQ_s37_r0
    positivity
  have hprob : ∑ c, alphaQ_s37_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7328675179,492671321506,492671190313,7328813002] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000057281,499999942719,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 37 1 c : ℚ) / 1000000000000

private def jointExponent_s37_r1 (c : MME.ReleasedInterior.Split 37) : ℕ :=
  [3, 2, 7, 7, 2, 3].getD ((seed 3 37).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s37_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 37 => c.val 0)
        (fun c => (splitWeight 3 37 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 37 => (splitWeight 3 37 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 37) : 0 ≤ alphaQ_s37_r1 c := by
    unfold alphaQ_s37_r1
    positivity
  have hprob : ∑ c, alphaQ_s37_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7370349398,492629650655,492629665880,7370334067] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999994982,500000005018,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 37 2 c : ℚ) / 1000000000000

private def jointExponent_s37_r2 (c : MME.ReleasedInterior.Split 37) : ℕ :=
  [3, 2, 7, 7, 2, 3].getD ((seed 3 37).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s37_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 37 => c.val 0)
        (fun c => (splitWeight 3 37 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 37 => (splitWeight 3 37 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 37) : 0 ≤ alphaQ_s37_r2 c := by
    unfold alphaQ_s37_r2
    positivity
  have hprob : ∑ c, alphaQ_s37_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7317715506,492682312445,492682219981,7317752068] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999980810,500000019190,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s37_r4 (c : MME.ReleasedInterior.Split 37) : ℚ :=
  (splitWeight 3 37 4 c : ℚ) / 1000000000000

private def jointExponent_s37_r4 (c : MME.ReleasedInterior.Split 37) : ℕ :=
  [3, 2, 7, 7, 2, 3].getD ((seed 3 37).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s37_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 37 => c.val 0)
        (fun c => (splitWeight 3 37 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 37 => (splitWeight 3 37 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 37) : 0 ≤ alphaQ_s37_r4 c := by
    unfold alphaQ_s37_r4
    positivity
  have hprob : ∑ c, alphaQ_s37_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7354859352,492645141781,492645160455,7354838412] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999993542,500000006458,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 37 5 c : ℚ) / 1000000000000

private def jointExponent_s37_r5 (c : MME.ReleasedInterior.Split 37) : ℕ :=
  [3, 2, 7, 7, 2, 3].getD ((seed 3 37).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s37_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 37 => c.val 0)
        (fun c => (splitWeight 3 37 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 37 => (splitWeight 3 37 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 37) : 0 ≤ alphaQ_s37_r5 c := by
    unfold alphaQ_s37_r5
    positivity
  have hprob : ∑ c, alphaQ_s37_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7257041050,492742950940,492742978081,7257029929] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000010194,499999989806,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 40 0 c : ℚ) / 1000000000000

private def jointExponent_s40_r0 (c : MME.ReleasedInterior.Split 40) : ℕ :=
  [1, 3, 3, 1].getD ((seed 3 40).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s40_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 40 => c.val 0)
        (fun c => (splitWeight 3 40 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 40 => (splitWeight 3 40 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 40) : 0 ≤ alphaQ_s40_r0 c := by
    unfold alphaQ_s40_r0
    positivity
  have hprob : ∑ c, alphaQ_s40_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500008327111,499991672889,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500006671669,499993328331,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 40 1 c : ℚ) / 1000000000000

private def jointExponent_s40_r1 (c : MME.ReleasedInterior.Split 40) : ℕ :=
  [1, 3, 3, 1].getD ((seed 3 40).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s40_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 40 => c.val 0)
        (fun c => (splitWeight 3 40 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 40 => (splitWeight 3 40 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 40) : 0 ≤ alphaQ_s40_r1 c := by
    unfold alphaQ_s40_r1
    positivity
  have hprob : ∑ c, alphaQ_s40_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499962976384,500037023616,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499970329721,500029670279,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 40 2 c : ℚ) / 1000000000000

private def jointExponent_s40_r2 (c : MME.ReleasedInterior.Split 40) : ℕ :=
  [1, 3, 3, 1].getD ((seed 3 40).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s40_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 40 => c.val 0)
        (fun c => (splitWeight 3 40 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 40 => (splitWeight 3 40 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 40) : 0 ≤ alphaQ_s40_r2 c := by
    unfold alphaQ_s40_r2
    positivity
  have hprob : ∑ c, alphaQ_s40_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500017037682,499982962318,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500014251462,499985748538,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 40 3 c : ℚ) / 1000000000000

private def jointExponent_s40_r3 (c : MME.ReleasedInterior.Split 40) : ℕ :=
  [1, 3, 3, 1].getD ((seed 3 40).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s40_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 40 => c.val 0)
        (fun c => (splitWeight 3 40 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 40 => (splitWeight 3 40 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 40) : 0 ≤ alphaQ_s40_r3 c := by
    unfold alphaQ_s40_r3
    positivity
  have hprob : ∑ c, alphaQ_s40_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500017096162,499982903838,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500014141000,499985859000,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 40 4 c : ℚ) / 1000000000000

private def jointExponent_s40_r4 (c : MME.ReleasedInterior.Split 40) : ℕ :=
  [1, 3, 3, 1].getD ((seed 3 40).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s40_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 40 => c.val 0)
        (fun c => (splitWeight 3 40 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 40 => (splitWeight 3 40 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 40) : 0 ≤ alphaQ_s40_r4 c := by
    unfold alphaQ_s40_r4
    positivity
  have hprob : ∑ c, alphaQ_s40_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499967443493,500032556507,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499973966290,500026033710,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 3 40 5 c : ℚ) / 1000000000000

private def jointExponent_s40_r5 (c : MME.ReleasedInterior.Split 40) : ℕ :=
  [1, 3, 3, 1].getD ((seed 3 40).splits.idxOf (sourceShape 3 c)) 0

private theorem region_s40_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 40 => c.val 0)
        (fun c => (splitWeight 3 40 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 40 => (splitWeight 3 40 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 40) : 0 ≤ alphaQ_s40_r5 c := by
    unfold alphaQ_s40_r5
    positivity
  have hprob : ∑ c, alphaQ_s40_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500008566288,499991433712,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500006775559,499993224441,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
    (s : Fin 45) (r : Fin 6) (hi : (seed 3 s).boundary = [])
    (hn : 0 < (seed 3 s).region.getD r.val 0) :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split s => c.val 0)
        (fun c => (splitWeight 3 s r c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split s => (splitWeight 3 s r c : ℝ) / 1000000000000) := by
  fin_cases s
  · exact False.elim ((by decide +kernel : (seed 3 0).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 3 1).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 3 2).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 3 3).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 3 4).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 3 5).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 3 6).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 3 7).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 3 8).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 3 9).boundary ≠ []) hi)
  · fin_cases r
    · exact region_s10_r0
    · exact region_s10_r1
    · exact region_s10_r2
    · exact region_s10_r3
    · exact region_s10_r4
    · exact region_s10_r5
  · fin_cases r
    · have hz : (seed 3 11).region.getD 0 0 = 0 := by decide +kernel
      change 0 < (seed 3 11).region.getD 0 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 3 11).region.getD 1 0 = 0 := by decide +kernel
      change 0 < (seed 3 11).region.getD 1 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 3 11).region.getD 2 0 = 0 := by decide +kernel
      change 0 < (seed 3 11).region.getD 2 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s11_r3
    · exact region_s11_r4
    · exact region_s11_r5
  · fin_cases r
    · have hz : (seed 3 12).region.getD 0 0 = 0 := by decide +kernel
      change 0 < (seed 3 12).region.getD 0 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 3 12).region.getD 1 0 = 0 := by decide +kernel
      change 0 < (seed 3 12).region.getD 1 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 3 12).region.getD 2 0 = 0 := by decide +kernel
      change 0 < (seed 3 12).region.getD 2 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s12_r3
    · exact region_s12_r4
    · exact region_s12_r5
  · fin_cases r
    · exact region_s13_r0
    · exact region_s13_r1
    · exact region_s13_r2
    · have hz : (seed 3 13).region.getD 3 0 = 0 := by decide +kernel
      change 0 < (seed 3 13).region.getD 3 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 3 13).region.getD 4 0 = 0 := by decide +kernel
      change 0 < (seed 3 13).region.getD 4 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 3 13).region.getD 5 0 = 0 := by decide +kernel
      change 0 < (seed 3 13).region.getD 5 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
  · fin_cases r
    · exact region_s14_r0
    · exact region_s14_r1
    · exact region_s14_r2
    · exact region_s14_r3
    · have hz : (seed 3 14).region.getD 4 0 = 0 := by decide +kernel
      change 0 < (seed 3 14).region.getD 4 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s14_r5
  · fin_cases r
    · exact region_s15_r0
    · exact region_s15_r1
    · exact region_s15_r2
    · exact region_s15_r3
    · exact region_s15_r4
    · exact region_s15_r5
  · exact False.elim ((by decide +kernel : (seed 3 16).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 3 17).boundary ≠ []) hi)
  · fin_cases r
    · have hz : (seed 3 18).region.getD 0 0 = 0 := by decide +kernel
      change 0 < (seed 3 18).region.getD 0 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 3 18).region.getD 1 0 = 0 := by decide +kernel
      change 0 < (seed 3 18).region.getD 1 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s18_r2
    · exact region_s18_r3
    · have hz : (seed 3 18).region.getD 4 0 = 0 := by decide +kernel
      change 0 < (seed 3 18).region.getD 4 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s18_r5
  · fin_cases r
    · have hz : (seed 3 19).region.getD 0 0 = 0 := by decide +kernel
      change 0 < (seed 3 19).region.getD 0 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 3 19).region.getD 1 0 = 0 := by decide +kernel
      change 0 < (seed 3 19).region.getD 1 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s19_r2
    · exact region_s19_r3
    · exact region_s19_r4
    · exact region_s19_r5
  · fin_cases r
    · exact region_s20_r0
    · exact region_s20_r1
    · have hz : (seed 3 20).region.getD 2 0 = 0 := by decide +kernel
      change 0 < (seed 3 20).region.getD 2 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 3 20).region.getD 3 0 = 0 := by decide +kernel
      change 0 < (seed 3 20).region.getD 3 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
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
    · exact region_s22_r4
    · have hz : (seed 3 22).region.getD 5 0 = 0 := by decide +kernel
      change 0 < (seed 3 22).region.getD 5 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
  · exact False.elim ((by decide +kernel : (seed 3 23).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 3 24).boundary ≠ []) hi)
  · fin_cases r
    · have hz : (seed 3 25).region.getD 0 0 = 0 := by decide +kernel
      change 0 < (seed 3 25).region.getD 0 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 3 25).region.getD 1 0 = 0 := by decide +kernel
      change 0 < (seed 3 25).region.getD 1 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s25_r2
    · exact region_s25_r3
    · have hz : (seed 3 25).region.getD 4 0 = 0 := by decide +kernel
      change 0 < (seed 3 25).region.getD 4 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s25_r5
  · fin_cases r
    · exact region_s26_r0
    · exact region_s26_r1
    · exact region_s26_r2
    · exact region_s26_r3
    · have hz : (seed 3 26).region.getD 4 0 = 0 := by decide +kernel
      change 0 < (seed 3 26).region.getD 4 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 3 26).region.getD 5 0 = 0 := by decide +kernel
      change 0 < (seed 3 26).region.getD 5 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
  · fin_cases r
    · have hz : (seed 3 27).region.getD 0 0 = 0 := by decide +kernel
      change 0 < (seed 3 27).region.getD 0 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 3 27).region.getD 1 0 = 0 := by decide +kernel
      change 0 < (seed 3 27).region.getD 1 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s27_r2
    · exact region_s27_r3
    · exact region_s27_r4
    · exact region_s27_r5
  · fin_cases r
    · exact region_s28_r0
    · have hz : (seed 3 28).region.getD 1 0 = 0 := by decide +kernel
      change 0 < (seed 3 28).region.getD 1 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s28_r2
    · exact region_s28_r3
    · have hz : (seed 3 28).region.getD 4 0 = 0 := by decide +kernel
      change 0 < (seed 3 28).region.getD 4 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 3 28).region.getD 5 0 = 0 := by decide +kernel
      change 0 < (seed 3 28).region.getD 5 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
  · exact False.elim ((by decide +kernel : (seed 3 29).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 3 30).boundary ≠ []) hi)
  · fin_cases r
    · exact region_s31_r0
    · exact region_s31_r1
    · have hz : (seed 3 31).region.getD 2 0 = 0 := by decide +kernel
      change 0 < (seed 3 31).region.getD 2 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 3 31).region.getD 3 0 = 0 := by decide +kernel
      change 0 < (seed 3 31).region.getD 3 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s31_r4
    · have hz : (seed 3 31).region.getD 5 0 = 0 := by decide +kernel
      change 0 < (seed 3 31).region.getD 5 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
  · fin_cases r
    · exact region_s32_r0
    · have hz : (seed 3 32).region.getD 1 0 = 0 := by decide +kernel
      change 0 < (seed 3 32).region.getD 1 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s32_r2
    · exact region_s32_r3
    · have hz : (seed 3 32).region.getD 4 0 = 0 := by decide +kernel
      change 0 < (seed 3 32).region.getD 4 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s32_r5
  · fin_cases r
    · have hz : (seed 3 33).region.getD 0 0 = 0 := by decide +kernel
      change 0 < (seed 3 33).region.getD 0 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s33_r1
    · have hz : (seed 3 33).region.getD 2 0 = 0 := by decide +kernel
      change 0 < (seed 3 33).region.getD 2 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 3 33).region.getD 3 0 = 0 := by decide +kernel
      change 0 < (seed 3 33).region.getD 3 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s33_r4
    · exact region_s33_r5
  · exact False.elim ((by decide +kernel : (seed 3 34).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 3 35).boundary ≠ []) hi)
  · fin_cases r
    · exact region_s36_r0
    · exact region_s36_r1
    · have hz : (seed 3 36).region.getD 2 0 = 0 := by decide +kernel
      change 0 < (seed 3 36).region.getD 2 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s36_r3
    · exact region_s36_r4
    · exact region_s36_r5
  · fin_cases r
    · exact region_s37_r0
    · exact region_s37_r1
    · exact region_s37_r2
    · have hz : (seed 3 37).region.getD 3 0 = 0 := by decide +kernel
      change 0 < (seed 3 37).region.getD 3 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s37_r4
    · exact region_s37_r5
  · exact False.elim ((by decide +kernel : (seed 3 38).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 3 39).boundary ≠ []) hi)
  · fin_cases r
    · exact region_s40_r0
    · exact region_s40_r1
    · exact region_s40_r2
    · exact region_s40_r3
    · exact region_s40_r4
    · exact region_s40_r5
  · exact False.elim ((by decide +kernel : (seed 3 41).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 3 42).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 3 43).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 3 44).boundary ≠ []) hi)


#print axioms solution
