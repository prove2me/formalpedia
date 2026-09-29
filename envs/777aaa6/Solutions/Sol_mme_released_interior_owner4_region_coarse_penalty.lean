-- Prove2me | solution 1 for mme_released_interior_owner4_region_coarse_penalty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T07:19:13.882734+00:00
-- url     : https://prove2.me/submissions/bf45b6ad-0ac5-4218-af53-9cbfbfbb4dbb

import Theorems.Thm_mme_rational_coarse_penalty_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME.RegionRate MME.RecursiveThinSplit MME.ReleasedInterior

private def alphaQ_s10_r0 (c : MME.ReleasedInterior.Split 10) : ℚ :=
  (splitWeight 4 10 0 c : ℚ) / 1000000000000

private def jointExponent_s10_r0 (c : MME.ReleasedInterior.Split 10) : ℕ :=
  [1, 3, 3, 1].getD ((seed 4 10).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s10_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 10 => c.val 0)
        (fun c => (splitWeight 4 10 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 10 => (splitWeight 4 10 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 10) : 0 ≤ alphaQ_s10_r0 c := by
    unfold alphaQ_s10_r0
    positivity
  have hprob : ∑ c, alphaQ_s10_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500454868974,499545131026,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500383937421,499616062579,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 10 1 c : ℚ) / 1000000000000

private def jointExponent_s10_r1 (c : MME.ReleasedInterior.Split 10) : ℕ :=
  [1, 3, 3, 1].getD ((seed 4 10).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s10_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 10 => c.val 0)
        (fun c => (splitWeight 4 10 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 10 => (splitWeight 4 10 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 10) : 0 ≤ alphaQ_s10_r1 c := by
    unfold alphaQ_s10_r1
    positivity
  have hprob : ∑ c, alphaQ_s10_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500417062644,499582937356,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500352409512,499647590488,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 10 2 c : ℚ) / 1000000000000

private def jointExponent_s10_r2 (c : MME.ReleasedInterior.Split 10) : ℕ :=
  [1, 3, 3, 1].getD ((seed 4 10).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s10_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 10 => c.val 0)
        (fun c => (splitWeight 4 10 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 10 => (splitWeight 4 10 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 10) : 0 ≤ alphaQ_s10_r2 c := by
    unfold alphaQ_s10_r2
    positivity
  have hprob : ∑ c, alphaQ_s10_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500403965490,499596034510,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500411068530,499588931470,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 10 3 c : ℚ) / 1000000000000

private def jointExponent_s10_r3 (c : MME.ReleasedInterior.Split 10) : ℕ :=
  [1, 3, 3, 1].getD ((seed 4 10).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s10_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 10 => c.val 0)
        (fun c => (splitWeight 4 10 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 10 => (splitWeight 4 10 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 10) : 0 ≤ alphaQ_s10_r3 c := by
    unfold alphaQ_s10_r3
    positivity
  have hprob : ∑ c, alphaQ_s10_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500465848551,499534151449,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500387702222,499612297778,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 10 4 c : ℚ) / 1000000000000

private def jointExponent_s10_r4 (c : MME.ReleasedInterior.Split 10) : ℕ :=
  [1, 3, 3, 1].getD ((seed 4 10).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s10_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 10 => c.val 0)
        (fun c => (splitWeight 4 10 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 10 => (splitWeight 4 10 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 10) : 0 ≤ alphaQ_s10_r4 c := by
    unfold alphaQ_s10_r4
    positivity
  have hprob : ∑ c, alphaQ_s10_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500417464940,499582535060,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500352187720,499647812280,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 10 5 c : ℚ) / 1000000000000

private def jointExponent_s10_r5 (c : MME.ReleasedInterior.Split 10) : ℕ :=
  [1, 3, 3, 1].getD ((seed 4 10).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s10_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 10 => c.val 0)
        (fun c => (splitWeight 4 10 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 10 => (splitWeight 4 10 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 10) : 0 ≤ alphaQ_s10_r5 c := by
    unfold alphaQ_s10_r5
    positivity
  have hprob : ∑ c, alphaQ_s10_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500457632740,499542367260,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500381247730,499618752270,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 11 0 c : ℚ) / 1000000000000

private def jointExponent_s11_r0 (c : MME.ReleasedInterior.Split 11) : ℕ :=
  [3, 7, 2, 2, 7, 3].getD ((seed 4 11).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s11_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 11 => c.val 0)
        (fun c => (splitWeight 4 11 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 11 => (splitWeight 4 11 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 11) : 0 ≤ alphaQ_s11_r0 c := by
    unfold alphaQ_s11_r0
    positivity
  have hprob : ∑ c, alphaQ_s11_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000016308,499999983692,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,6634080341,493365965839,493365684107,6634269713] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s11_r1 (c : MME.ReleasedInterior.Split 11) : ℚ :=
  (splitWeight 4 11 1 c : ℚ) / 1000000000000

private def jointExponent_s11_r1 (c : MME.ReleasedInterior.Split 11) : ℕ :=
  [3, 7, 2, 2, 7, 3].getD ((seed 4 11).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s11_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 11 => c.val 0)
        (fun c => (splitWeight 4 11 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 11 => (splitWeight 4 11 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 11) : 0 ≤ alphaQ_s11_r1 c := by
    unfold alphaQ_s11_r1
    positivity
  have hprob : ∑ c, alphaQ_s11_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999999249,500000000751,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,6611909494,493388087407,493388060329,6611942770] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 11 4 c : ℚ) / 1000000000000

private def jointExponent_s11_r4 (c : MME.ReleasedInterior.Split 11) : ℕ :=
  [3, 7, 2, 2, 7, 3].getD ((seed 4 11).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s11_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 11 => c.val 0)
        (fun c => (splitWeight 4 11 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 11 => (splitWeight 4 11 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 11) : 0 ≤ alphaQ_s11_r4 c := by
    unfold alphaQ_s11_r4
    positivity
  have hprob : ∑ c, alphaQ_s11_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999947665,500000052335,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,6588078272,493411838713,493412324618,6587758397] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s12_r0 (c : MME.ReleasedInterior.Split 12) : ℚ :=
  (splitWeight 4 12 0 c : ℚ) / 1000000000000

private def jointExponent_s12_r0 (c : MME.ReleasedInterior.Split 12) : ℕ :=
  [6, 12, 1, 4, 4, 1, 12, 6].getD ((seed 4 12).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s12_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 12 => c.val 0)
        (fun c => (splitWeight 4 12 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 12 => (splitWeight 4 12 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 12) : 0 ≤ alphaQ_s12_r0 c := by
    unfold alphaQ_s12_r0
    positivity
  have hprob : ∑ c, alphaQ_s12_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999993415,500000006585,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![325646084,70612000910,858124706584,70611997515,325648907] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s12_r1 (c : MME.ReleasedInterior.Split 12) : ℚ :=
  (splitWeight 4 12 1 c : ℚ) / 1000000000000

private def jointExponent_s12_r1 (c : MME.ReleasedInterior.Split 12) : ℕ :=
  [6, 12, 1, 4, 4, 1, 12, 6].getD ((seed 4 12).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s12_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 12 => c.val 0)
        (fun c => (splitWeight 4 12 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 12 => (splitWeight 4 12 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 12) : 0 ≤ alphaQ_s12_r1 c := by
    unfold alphaQ_s12_r1
    positivity
  have hprob : ∑ c, alphaQ_s12_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000023452,499999976548,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![323417201,73598743598,852155694676,73598719376,323425149] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 12 4 c : ℚ) / 1000000000000

private def jointExponent_s12_r4 (c : MME.ReleasedInterior.Split 12) : ℕ :=
  [6, 12, 1, 4, 4, 1, 12, 6].getD ((seed 4 12).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s12_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 12 => c.val 0)
        (fun c => (splitWeight 4 12 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 12 => (splitWeight 4 12 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 12) : 0 ≤ alphaQ_s12_r4 c := by
    unfold alphaQ_s12_r4
    positivity
  have hprob : ∑ c, alphaQ_s12_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000022298,499999977702,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![326224099,73581346795,852184873116,73581337792,326218198] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s13_r2 (c : MME.ReleasedInterior.Split 13) : ℚ :=
  (splitWeight 4 13 2 c : ℚ) / 1000000000000

private def jointExponent_s13_r2 (c : MME.ReleasedInterior.Split 13) : ℕ :=
  [12, 4, 6, 1, 1, 6, 4, 12].getD ((seed 4 13).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s13_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 13 => c.val 0)
        (fun c => (splitWeight 4 13 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 13 => (splitWeight 4 13 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 13) : 0 ≤ alphaQ_s13_r2 c := by
    unfold alphaQ_s13_r2
    positivity
  have hprob : ∑ c, alphaQ_s13_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000016845,499999983155,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![323995926,74871046497,849609922309,74871036719,323998549] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 13 3 c : ℚ) / 1000000000000

private def jointExponent_s13_r3 (c : MME.ReleasedInterior.Split 13) : ℕ :=
  [12, 4, 6, 1, 1, 6, 4, 12].getD ((seed 4 13).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s13_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 13 => c.val 0)
        (fun c => (splitWeight 4 13 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 13 => (splitWeight 4 13 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 13) : 0 ≤ alphaQ_s13_r3 c := by
    unfold alphaQ_s13_r3
    positivity
  have hprob : ∑ c, alphaQ_s13_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000042026,499999957974,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![325720883,77662867271,844022843322,77662845577,325722947] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s13_r5 (c : MME.ReleasedInterior.Split 13) : ℚ :=
  (splitWeight 4 13 5 c : ℚ) / 1000000000000

private def jointExponent_s13_r5 (c : MME.ReleasedInterior.Split 13) : ℕ :=
  [12, 4, 6, 1, 1, 6, 4, 12].getD ((seed 4 13).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s13_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 13 => c.val 0)
        (fun c => (splitWeight 4 13 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 13 => (splitWeight 4 13 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 13) : 0 ≤ alphaQ_s13_r5 c := by
    unfold alphaQ_s13_r5
    positivity
  have hprob : ∑ c, alphaQ_s13_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000002022,499999997978,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![327355715,77707301304,843930687884,77707300636,327354461] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s14_r1 (c : MME.ReleasedInterior.Split 14) : ℚ :=
  (splitWeight 4 14 1 c : ℚ) / 1000000000000

private def jointExponent_s14_r1 (c : MME.ReleasedInterior.Split 14) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 4 14).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s14_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 14 => c.val 0)
        (fun c => (splitWeight 4 14 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 14 => (splitWeight 4 14 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 14) : 0 ≤ alphaQ_s14_r1 c := by
    unfold alphaQ_s14_r1
    positivity
  have hprob : ∑ c, alphaQ_s14_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999997618,500000002382,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,7158471649,492841469578,492841573967,7158484806] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 14 2 c : ℚ) / 1000000000000

private def jointExponent_s14_r2 (c : MME.ReleasedInterior.Split 14) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 4 14).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s14_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 14 => c.val 0)
        (fun c => (splitWeight 4 14 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 14 => (splitWeight 4 14 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 14) : 0 ≤ alphaQ_s14_r2 c := by
    unfold alphaQ_s14_r2
    positivity
  have hprob : ∑ c, alphaQ_s14_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000004111,499999995889,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,7039400019,492960620084,492960517662,7039462235] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 14 3 c : ℚ) / 1000000000000

private def jointExponent_s14_r3 (c : MME.ReleasedInterior.Split 14) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 4 14).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s14_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 14 => c.val 0)
        (fun c => (splitWeight 4 14 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 14 => (splitWeight 4 14 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 14) : 0 ≤ alphaQ_s14_r3 c := by
    unfold alphaQ_s14_r3
    positivity
  have hprob : ∑ c, alphaQ_s14_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999990700,500000009300,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,7071908476,492928081479,492928165060,7071844985] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 14 4 c : ℚ) / 1000000000000

private def jointExponent_s14_r4 (c : MME.ReleasedInterior.Split 14) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 4 14).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s14_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 14 => c.val 0)
        (fun c => (splitWeight 4 14 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 14 => (splitWeight 4 14 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 14) : 0 ≤ alphaQ_s14_r4 c := by
    unfold alphaQ_s14_r4
    positivity
  have hprob : ∑ c, alphaQ_s14_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000005760,499999994240,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,7160152273,492839879641,492839708258,7160259828] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 14 5 c : ℚ) / 1000000000000

private def jointExponent_s14_r5 (c : MME.ReleasedInterior.Split 14) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 4 14).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s14_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 14 => c.val 0)
        (fun c => (splitWeight 4 14 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 14 => (splitWeight 4 14 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 14) : 0 ≤ alphaQ_s14_r5 c := by
    unfold alphaQ_s14_r5
    positivity
  have hprob : ∑ c, alphaQ_s14_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000005805,499999994195,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,7071714340,492928290945,492928257172,7071737543] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 15 0 c : ℚ) / 1000000000000

private def jointExponent_s15_r0 (c : MME.ReleasedInterior.Split 15) : ℕ :=
  [3, 1, 1, 3].getD ((seed 4 15).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s15_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 15 => c.val 0)
        (fun c => (splitWeight 4 15 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 15 => (splitWeight 4 15 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 15) : 0 ≤ alphaQ_s15_r0 c := by
    unfold alphaQ_s15_r0
    positivity
  have hprob : ∑ c, alphaQ_s15_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999998216,500000001784,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999998235,500000001765,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 15 1 c : ℚ) / 1000000000000

private def jointExponent_s15_r1 (c : MME.ReleasedInterior.Split 15) : ℕ :=
  [3, 1, 1, 3].getD ((seed 4 15).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s15_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 15 => c.val 0)
        (fun c => (splitWeight 4 15 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 15 => (splitWeight 4 15 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 15) : 0 ≤ alphaQ_s15_r1 c := by
    unfold alphaQ_s15_r1
    positivity
  have hprob : ∑ c, alphaQ_s15_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999996121,500000003879,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999996140,500000003860,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 15 2 c : ℚ) / 1000000000000

private def jointExponent_s15_r2 (c : MME.ReleasedInterior.Split 15) : ℕ :=
  [3, 1, 1, 3].getD ((seed 4 15).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s15_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 15 => c.val 0)
        (fun c => (splitWeight 4 15 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 15 => (splitWeight 4 15 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 15) : 0 ≤ alphaQ_s15_r2 c := by
    unfold alphaQ_s15_r2
    positivity
  have hprob : ∑ c, alphaQ_s15_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999997203,500000002797,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999998337,500000001663,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 15 3 c : ℚ) / 1000000000000

private def jointExponent_s15_r3 (c : MME.ReleasedInterior.Split 15) : ℕ :=
  [3, 1, 1, 3].getD ((seed 4 15).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s15_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 15 => c.val 0)
        (fun c => (splitWeight 4 15 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 15 => (splitWeight 4 15 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 15) : 0 ≤ alphaQ_s15_r3 c := by
    unfold alphaQ_s15_r3
    positivity
  have hprob : ∑ c, alphaQ_s15_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999995931,500000004069,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999995948,500000004052,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 15 4 c : ℚ) / 1000000000000

private def jointExponent_s15_r4 (c : MME.ReleasedInterior.Split 15) : ℕ :=
  [3, 1, 1, 3].getD ((seed 4 15).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s15_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 15 => c.val 0)
        (fun c => (splitWeight 4 15 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 15 => (splitWeight 4 15 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 15) : 0 ≤ alphaQ_s15_r4 c := by
    unfold alphaQ_s15_r4
    positivity
  have hprob : ∑ c, alphaQ_s15_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999995540,500000004460,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999995579,500000004421,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 15 5 c : ℚ) / 1000000000000

private def jointExponent_s15_r5 (c : MME.ReleasedInterior.Split 15) : ℕ :=
  [3, 1, 1, 3].getD ((seed 4 15).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s15_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 15 => c.val 0)
        (fun c => (splitWeight 4 15 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 15 => (splitWeight 4 15 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 15) : 0 ≤ alphaQ_s15_r5 c := by
    unfold alphaQ_s15_r5
    positivity
  have hprob : ∑ c, alphaQ_s15_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999995936,500000004064,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999995942,500000004058,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s18_r1 (c : MME.ReleasedInterior.Split 18) : ℚ :=
  (splitWeight 4 18 1 c : ℚ) / 1000000000000

private def jointExponent_s18_r1 (c : MME.ReleasedInterior.Split 18) : ℕ :=
  [3, 2, 7, 7, 2, 3].getD ((seed 4 18).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s18_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 18 => c.val 0)
        (fun c => (splitWeight 4 18 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 18 => (splitWeight 4 18 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 18) : 0 ≤ alphaQ_s18_r1 c := by
    unfold alphaQ_s18_r1
    positivity
  have hprob : ∑ c, alphaQ_s18_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000005103,499999994897,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,6597669705,493402330884,493402312165,6597687246] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 18 4 c : ℚ) / 1000000000000

private def jointExponent_s18_r4 (c : MME.ReleasedInterior.Split 18) : ℕ :=
  [3, 2, 7, 7, 2, 3].getD ((seed 4 18).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s18_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 18 => c.val 0)
        (fun c => (splitWeight 4 18 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 18 => (splitWeight 4 18 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 18) : 0 ≤ alphaQ_s18_r4 c := by
    unfold alphaQ_s18_r4
    positivity
  have hprob : ∑ c, alphaQ_s18_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999998281,500000001719,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,6619426027,493380561723,493380620664,6619391586] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 18 5 c : ℚ) / 1000000000000

private def jointExponent_s18_r5 (c : MME.ReleasedInterior.Split 18) : ℕ :=
  [3, 2, 7, 7, 2, 3].getD ((seed 4 18).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s18_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 18 => c.val 0)
        (fun c => (splitWeight 4 18 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 18 => (splitWeight 4 18 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 18) : 0 ≤ alphaQ_s18_r5 c := by
    unfold alphaQ_s18_r5
    positivity
  have hprob : ∑ c, alphaQ_s18_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000000231,499999999769,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![0,6637793307,493362196517,493362246706,6637763470] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s19_r0 (c : MME.ReleasedInterior.Split 19) : ℚ :=
  (splitWeight 4 19 0 c : ℚ) / 1000000000000

private def jointExponent_s19_r0 (c : MME.ReleasedInterior.Split 19) : ℕ :=
  [3, 5, 12, 5, 1, 5, 12, 5, 3].getD ((seed 4 19).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s19_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 19 => c.val 0)
        (fun c => (splitWeight 4 19 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 19 => (splitWeight 4 19 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 19) : 0 ≤ alphaQ_s19_r0 c := by
    unfold alphaQ_s19_r0
    positivity
  have hprob : ∑ c, alphaQ_s19_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![180463079202,639073829625,180463091173,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![318804818,71761505044,855839428591,71761426703,318834844] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s19_r0 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![3,1,3,0,0] ![3,1,3,40,40] ![12,4,0,4,12] jointExponent_s19_r0 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 19 => c.val 0)
        (fun c => (alphaQ_s19_r0 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s19_r0 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s19_r0, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s19_r1 (c : MME.ReleasedInterior.Split 19) : ℚ :=
  (splitWeight 4 19 1 c : ℚ) / 1000000000000

private def jointExponent_s19_r1 (c : MME.ReleasedInterior.Split 19) : ℕ :=
  [3, 5, 12, 5, 1, 5, 12, 5, 3].getD ((seed 4 19).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s19_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 19 => c.val 0)
        (fun c => (splitWeight 4 19 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 19 => (splitWeight 4 19 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 19) : 0 ≤ alphaQ_s19_r1 c := by
    unfold alphaQ_s19_r1
    positivity
  have hprob : ∑ c, alphaQ_s19_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![183348535603,633302956421,183348507976,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![319717447,72982958683,853394652490,72982892783,319778597] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s19_r1 ha hprob 1 2
    (by decide) p q hp hq hpmass hqmass ![3,1,3,0,0] ![3,1,3,40,40] ![12,4,0,4,12] jointExponent_s19_r1 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 19 => c.val 0)
        (fun c => (alphaQ_s19_r1 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s19_r1 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s19_r1, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s19_r4 (c : MME.ReleasedInterior.Split 19) : ℚ :=
  (splitWeight 4 19 4 c : ℚ) / 1000000000000

private def jointExponent_s19_r4 (c : MME.ReleasedInterior.Split 19) : ℕ :=
  [3, 5, 12, 5, 1, 5, 12, 5, 3].getD ((seed 4 19).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s19_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 19 => c.val 0)
        (fun c => (splitWeight 4 19 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 19 => (splitWeight 4 19 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 19) : 0 ≤ alphaQ_s19_r4 c := by
    unfold alphaQ_s19_r4
    positivity
  have hprob : ∑ c, alphaQ_s19_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![183317850179,633364330640,183317819181,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![319695275,72979637148,853401340649,72979565427,319761501] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 19 5 c : ℚ) / 1000000000000

private def jointExponent_s19_r5 (c : MME.ReleasedInterior.Split 19) : ℕ :=
  [3, 5, 12, 5, 1, 5, 12, 5, 3].getD ((seed 4 19).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s19_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 19 => c.val 0)
        (fun c => (splitWeight 4 19 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 19 => (splitWeight 4 19 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 19) : 0 ≤ alphaQ_s19_r5 c := by
    unfold alphaQ_s19_r5
    positivity
  have hprob : ∑ c, alphaQ_s19_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![180431905806,639136180257,180431913937,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![318731306,71757376108,855847818026,71757322137,318752423] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 20 0 c : ℚ) / 1000000000000

private def jointExponent_s20_r0 (c : MME.ReleasedInterior.Split 20) : ℕ :=
  [7, 9, 3, 2, 7, 7, 2, 3, 9, 7].getD ((seed 4 20).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s20_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 20 => c.val 0)
        (fun c => (splitWeight 4 20 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 20 => (splitWeight 4 20 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 20) : 0 ≤ alphaQ_s20_r0 c := by
    unfold alphaQ_s20_r0
    positivity
  have hprob : ∑ c, alphaQ_s20_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![12288397369,487711616801,487711647919,12288337911,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![12956747015,487043246701,487043183419,12956822865,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 20 1 c : ℚ) / 1000000000000

private def jointExponent_s20_r1 (c : MME.ReleasedInterior.Split 20) : ℕ :=
  [7, 9, 3, 2, 6, 6, 2, 3, 9, 7].getD ((seed 4 20).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s20_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 20 => c.val 0)
        (fun c => (splitWeight 4 20 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 20 => (splitWeight 4 20 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 20) : 0 ≤ alphaQ_s20_r1 c := by
    unfold alphaQ_s20_r1
    positivity
  have hprob : ∑ c, alphaQ_s20_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![12738379860,487261644710,487261681164,12738294266,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![13575158804,486424828061,486424752648,13575260487,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 20 2 c : ℚ) / 1000000000000

private def jointExponent_s20_r2 (c : MME.ReleasedInterior.Split 20) : ℕ :=
  [7, 9, 3, 2, 7, 7, 2, 3, 9, 7].getD ((seed 4 20).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s20_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 20 => c.val 0)
        (fun c => (splitWeight 4 20 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 20 => (splitWeight 4 20 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 20) : 0 ≤ alphaQ_s20_r2 c := by
    unfold alphaQ_s20_r2
    positivity
  have hprob : ∑ c, alphaQ_s20_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![13041373052,486958631802,486958621835,13041373311,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![12229216813,487770785322,487770762642,12229235223,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 20 3 c : ℚ) / 1000000000000

private def jointExponent_s20_r3 (c : MME.ReleasedInterior.Split 20) : ℕ :=
  [6, 9, 3, 2, 7, 7, 2, 3, 9, 6].getD ((seed 4 20).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s20_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 20 => c.val 0)
        (fun c => (splitWeight 4 20 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 20 => (splitWeight 4 20 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 20) : 0 ≤ alphaQ_s20_r3 c := by
    unfold alphaQ_s20_r3
    positivity
  have hprob : ∑ c, alphaQ_s20_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![13654441992,486345561679,486345545472,13654450857,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![12670437741,487329565495,487329551300,12670445464,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 21 0 c : ℚ) / 1000000000000

private def jointExponent_s21_r0 (c : MME.ReleasedInterior.Split 21) : ℕ :=
  [12, 5, 5, 3, 1, 3, 5, 5, 12].getD ((seed 4 21).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s21_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 21 => c.val 0)
        (fun c => (splitWeight 4 21 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 21 => (splitWeight 4 21 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 21) : 0 ≤ alphaQ_s21_r0 c := by
    unfold alphaQ_s21_r0
    positivity
  have hprob : ∑ c, alphaQ_s21_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![328678745,76800048281,845742536248,76800136038,328600688] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![181703302394,636593361789,181703335817,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 21 1 c : ℚ) / 1000000000000

private def jointExponent_s21_r1 (c : MME.ReleasedInterior.Split 21) : ℕ :=
  [12, 5, 5, 3, 1, 3, 5, 5, 12].getD ((seed 4 21).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s21_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 21 => c.val 0)
        (fun c => (splitWeight 4 21 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 21 => (splitWeight 4 21 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 21) : 0 ≤ alphaQ_s21_r1 c := by
    unfold alphaQ_s21_r1
    positivity
  have hprob : ∑ c, alphaQ_s21_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![181623098860,636753763785,181623137355,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![328632626,76800519260,845741694232,76800600059,328553823] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 21 2 c : ℚ) / 1000000000000

private def jointExponent_s21_r2 (c : MME.ReleasedInterior.Split 21) : ℕ :=
  [12, 5, 5, 3, 1, 3, 5, 5, 12].getD ((seed 4 21).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s21_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 21 => c.val 0)
        (fun c => (splitWeight 4 21 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 21 => (splitWeight 4 21 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 21) : 0 ≤ alphaQ_s21_r2 c := by
    unfold alphaQ_s21_r2
    positivity
  have hprob : ∑ c, alphaQ_s21_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![328771031,76187470046,846967519760,76187444520,328794643] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![180589097958,638821815651,180589086391,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 21 3 c : ℚ) / 1000000000000

private def jointExponent_s21_r3 (c : MME.ReleasedInterior.Split 21) : ℕ :=
  [12, 5, 5, 3, 1, 3, 5, 5, 12].getD ((seed 4 21).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s21_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 21 => c.val 0)
        (fun c => (splitWeight 4 21 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 21 => (splitWeight 4 21 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 21) : 0 ≤ alphaQ_s21_r3 c := by
    unfold alphaQ_s21_r3
    positivity
  have hprob : ∑ c, alphaQ_s21_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![333674011,77544131975,844244389227,77544120731,333684056] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![183437508099,633124987990,183437503911,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 21 4 c : ℚ) / 1000000000000

private def jointExponent_s21_r4 (c : MME.ReleasedInterior.Split 21) : ℕ :=
  [12, 5, 5, 3, 1, 3, 5, 5, 12].getD ((seed 4 21).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s21_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 21 => c.val 0)
        (fun c => (splitWeight 4 21 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 21 => (splitWeight 4 21 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 21) : 0 ≤ alphaQ_s21_r4 c := by
    unfold alphaQ_s21_r4
    positivity
  have hprob : ∑ c, alphaQ_s21_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![180482608497,639034790747,180482600756,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![328694037,76187250356,846968116712,76187216984,328721911] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 21 5 c : ℚ) / 1000000000000

private def jointExponent_s21_r5 (c : MME.ReleasedInterior.Split 21) : ℕ :=
  [12, 5, 5, 3, 1, 3, 5, 5, 12].getD ((seed 4 21).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s21_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 21 => c.val 0)
        (fun c => (splitWeight 4 21 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 21 => (splitWeight 4 21 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 21) : 0 ≤ alphaQ_s21_r5 c := by
    unfold alphaQ_s21_r5
    positivity
  have hprob : ∑ c, alphaQ_s21_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![183371082958,633257872039,183371045003,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![333632898,77541237457,844250259306,77541163143,333707196] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 22 0 c : ℚ) / 1000000000000

private def jointExponent_s22_r0 (c : MME.ReleasedInterior.Split 22) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 4 22).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s22_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 22 => c.val 0)
        (fun c => (splitWeight 4 22 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 22 => (splitWeight 4 22 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 22) : 0 ≤ alphaQ_s22_r0 c := by
    unfold alphaQ_s22_r0
    positivity
  have hprob : ∑ c, alphaQ_s22_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7155556365,492844371431,492844509056,7155563148] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000008905,499999991095,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s22_r2 (c : MME.ReleasedInterior.Split 22) : ℚ :=
  (splitWeight 4 22 2 c : ℚ) / 1000000000000

private def jointExponent_s22_r2 (c : MME.ReleasedInterior.Split 22) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 4 22).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s22_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 22 => c.val 0)
        (fun c => (splitWeight 4 22 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 22 => (splitWeight 4 22 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 22) : 0 ≤ alphaQ_s22_r2 c := by
    unfold alphaQ_s22_r2
    positivity
  have hprob : ∑ c, alphaQ_s22_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7157373645,492842546744,492842690221,7157389390] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000055235,499999944765,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 22 3 c : ℚ) / 1000000000000

private def jointExponent_s22_r3 (c : MME.ReleasedInterior.Split 22) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 4 22).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s22_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 22 => c.val 0)
        (fun c => (splitWeight 4 22 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 22 => (splitWeight 4 22 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 22) : 0 ≤ alphaQ_s22_r3 c := by
    unfold alphaQ_s22_r3
    positivity
  have hprob : ∑ c, alphaQ_s22_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7069826405,492930176136,492930164613,7069832846] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000002375,499999997625,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 22 4 c : ℚ) / 1000000000000

private def jointExponent_s22_r4 (c : MME.ReleasedInterior.Split 22) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 4 22).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s22_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 22 => c.val 0)
        (fun c => (splitWeight 4 22 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 22 => (splitWeight 4 22 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 22) : 0 ≤ alphaQ_s22_r4 c := by
    unfold alphaQ_s22_r4
    positivity
  have hprob : ∑ c, alphaQ_s22_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7035067551,492964924803,492964921451,7035086195] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000014351,499999985649,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 22 5 c : ℚ) / 1000000000000

private def jointExponent_s22_r5 (c : MME.ReleasedInterior.Split 22) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 4 22).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s22_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 22 => c.val 0)
        (fun c => (splitWeight 4 22 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 22 => (splitWeight 4 22 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 22) : 0 ≤ alphaQ_s22_r5 c := by
    unfold alphaQ_s22_r5
    positivity
  have hprob : ∑ c, alphaQ_s22_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7070258438,492929747589,492929707267,7070286706] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000007202,499999992798,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s25_r1 (c : MME.ReleasedInterior.Split 25) : ℚ :=
  (splitWeight 4 25 1 c : ℚ) / 1000000000000

private def jointExponent_s25_r1 (c : MME.ReleasedInterior.Split 25) : ℕ :=
  [6, 1, 4, 12, 12, 4, 1, 6].getD ((seed 4 25).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s25_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 25 => c.val 0)
        (fun c => (splitWeight 4 25 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 25 => (splitWeight 4 25 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 25) : 0 ≤ alphaQ_s25_r1 c := by
    unfold alphaQ_s25_r1
    positivity
  have hprob : ∑ c, alphaQ_s25_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999774869,500000225131,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![328133964,73617829631,852107970824,73617879183,328186398] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 25 4 c : ℚ) / 1000000000000

private def jointExponent_s25_r4 (c : MME.ReleasedInterior.Split 25) : ℕ :=
  [6, 1, 4, 12, 12, 4, 1, 6].getD ((seed 4 25).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s25_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 25 => c.val 0)
        (fun c => (splitWeight 4 25 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 25 => (splitWeight 4 25 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 25) : 0 ≤ alphaQ_s25_r4 c := by
    unfold alphaQ_s25_r4
    positivity
  have hprob : ∑ c, alphaQ_s25_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000043167,499999956833,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![325134192,73631336974,852087100467,73631326884,325101483] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 25 5 c : ℚ) / 1000000000000

private def jointExponent_s25_r5 (c : MME.ReleasedInterior.Split 25) : ℕ :=
  [6, 1, 4, 12, 12, 4, 1, 6].getD ((seed 4 25).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s25_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 25 => c.val 0)
        (fun c => (splitWeight 4 25 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 25 => (splitWeight 4 25 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 25) : 0 ≤ alphaQ_s25_r5 c := by
    unfold alphaQ_s25_r5
    positivity
  have hprob : ∑ c, alphaQ_s25_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500000014023,499999985977,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![328252768,70622828027,858097856268,70622867460,328195477] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s26_r2 (c : MME.ReleasedInterior.Split 26) : ℚ :=
  (splitWeight 4 26 2 c : ℚ) / 1000000000000

private def jointExponent_s26_r2 (c : MME.ReleasedInterior.Split 26) : ℕ :=
  [6, 3, 7, 9, 2, 2, 9, 7, 3, 6].getD ((seed 4 26).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s26_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 26 => c.val 0)
        (fun c => (splitWeight 4 26 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 26 => (splitWeight 4 26 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 26) : 0 ≤ alphaQ_s26_r2 c := by
    unfold alphaQ_s26_r2
    positivity
  have hprob : ∑ c, alphaQ_s26_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![13771931459,486228221233,486228827934,13771019374,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![12678590339,487321235004,487320620528,12679554129,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 26 3 c : ℚ) / 1000000000000

private def jointExponent_s26_r3 (c : MME.ReleasedInterior.Split 26) : ℕ :=
  [7, 3, 7, 9, 2, 2, 9, 7, 3, 7].getD ((seed 4 26).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s26_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 26 => c.val 0)
        (fun c => (splitWeight 4 26 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 26 => (splitWeight 4 26 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 26) : 0 ≤ alphaQ_s26_r3 c := by
    unfold alphaQ_s26_r3
    positivity
  have hprob : ∑ c, alphaQ_s26_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![13161479382,486838652133,486839226889,13160641596,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![12245448718,487754423292,487753806276,12246321714,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s26_r4 (c : MME.ReleasedInterior.Split 26) : ℚ :=
  (splitWeight 4 26 4 c : ℚ) / 1000000000000

private def jointExponent_s26_r4 (c : MME.ReleasedInterior.Split 26) : ℕ :=
  [7, 3, 6, 9, 2, 2, 9, 6, 3, 7].getD ((seed 4 26).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s26_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 26 => c.val 0)
        (fun c => (splitWeight 4 26 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 26 => (splitWeight 4 26 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 26) : 0 ≤ alphaQ_s26_r4 c := by
    unfold alphaQ_s26_r4
    positivity
  have hprob : ∑ c, alphaQ_s26_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![12848663888,487151361243,487151418681,12848556188,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![13575472232,486424513563,486424420118,13575594087,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 26 5 c : ℚ) / 1000000000000

private def jointExponent_s26_r5 (c : MME.ReleasedInterior.Split 26) : ℕ :=
  [7, 3, 7, 9, 2, 2, 9, 7, 3, 7].getD ((seed 4 26).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s26_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 26 => c.val 0)
        (fun c => (splitWeight 4 26 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 26 => (splitWeight 4 26 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 26) : 0 ≤ alphaQ_s26_r5 c := by
    unfold alphaQ_s26_r5
    positivity
  have hprob : ∑ c, alphaQ_s26_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![12394078214,487605948250,487606035380,12393938156,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![12956472732,487043507685,487043395867,12956623716,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 27 0 c : ℚ) / 1000000000000

private def jointExponent_s27_r0 (c : MME.ReleasedInterior.Split 27) : ℕ :=
  [9, 7, 6, 2, 3, 3, 2, 6, 7, 9].getD ((seed 4 27).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s27_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 27 => c.val 0)
        (fun c => (splitWeight 4 27 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 27 => (splitWeight 4 27 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 27) : 0 ≤ alphaQ_s27_r0 c := by
    unfold alphaQ_s27_r0
    positivity
  have hprob : ∑ c, alphaQ_s27_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![13776084199,486223910753,486223911688,13776093360,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![12748935650,487251066199,487251081155,12748916996,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 27 1 c : ℚ) / 1000000000000

private def jointExponent_s27_r1 (c : MME.ReleasedInterior.Split 27) : ℕ :=
  [9, 7, 7, 2, 3, 3, 2, 7, 7, 9].getD ((seed 4 27).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s27_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 27 => c.val 0)
        (fun c => (splitWeight 4 27 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 27 => (splitWeight 4 27 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 27) : 0 ≤ alphaQ_s27_r1 c := by
    unfold alphaQ_s27_r1
    positivity
  have hprob : ∑ c, alphaQ_s27_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![13160187271,486839805981,486839775283,13160231465,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![12312061931,487687944327,487687980411,12312013331,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 27 4 c : ℚ) / 1000000000000

private def jointExponent_s27_r4 (c : MME.ReleasedInterior.Split 27) : ℕ :=
  [9, 7, 7, 2, 3, 3, 2, 7, 7, 9].getD ((seed 4 27).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s27_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 27 => c.val 0)
        (fun c => (splitWeight 4 27 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 27 => (splitWeight 4 27 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 27) : 0 ≤ alphaQ_s27_r4 c := by
    unfold alphaQ_s27_r4
    positivity
  have hprob : ∑ c, alphaQ_s27_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![12401840701,487598154659,487598154286,12401850354,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![13042223309,486957775869,486957799383,13042201439,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 27 5 c : ℚ) / 1000000000000

private def jointExponent_s27_r5 (c : MME.ReleasedInterior.Split 27) : ℕ :=
  [9, 6, 7, 2, 3, 3, 2, 7, 6, 9].getD ((seed 4 27).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s27_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 27 => c.val 0)
        (fun c => (splitWeight 4 27 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 27 => (splitWeight 4 27 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 27) : 0 ≤ alphaQ_s27_r5 c := by
    unfold alphaQ_s27_r5
    positivity
  have hprob : ∑ c, alphaQ_s27_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![12852180631,487147815338,487147803368,12852200663,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![13660562110,486339442093,486339451964,13660543833,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s28_r3 (c : MME.ReleasedInterior.Split 28) : ℚ :=
  (splitWeight 4 28 3 c : ℚ) / 1000000000000

private def jointExponent_s28_r3 (c : MME.ReleasedInterior.Split 28) : ℕ :=
  [12, 6, 4, 1, 1, 4, 6, 12].getD ((seed 4 28).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s28_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 28 => c.val 0)
        (fun c => (splitWeight 4 28 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 28 => (splitWeight 4 28 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 28) : 0 ≤ alphaQ_s28_r3 c := by
    unfold alphaQ_s28_r3
    positivity
  have hprob : ∑ c, alphaQ_s28_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![330623405,77757067348,843824626042,77757058236,330624969] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000016730,499999983270,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s28_r4 (c : MME.ReleasedInterior.Split 28) : ℚ :=
  (splitWeight 4 28 4 c : ℚ) / 1000000000000

private def jointExponent_s28_r4 (c : MME.ReleasedInterior.Split 28) : ℕ :=
  [12, 6, 4, 1, 1, 4, 6, 12].getD ((seed 4 28).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s28_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 28 => c.val 0)
        (fun c => (splitWeight 4 28 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 28 => (splitWeight 4 28 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 28) : 0 ≤ alphaQ_s28_r4 c := by
    unfold alphaQ_s28_r4
    positivity
  have hprob : ∑ c, alphaQ_s28_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![328224400,74882233854,849579079614,74882242539,328219593] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999992823,500000007177,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 28 5 c : ℚ) / 1000000000000

private def jointExponent_s28_r5 (c : MME.ReleasedInterior.Split 28) : ℕ :=
  [12, 6, 4, 1, 1, 4, 6, 12].getD ((seed 4 28).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s28_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 28 => c.val 0)
        (fun c => (splitWeight 4 28 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 28 => (splitWeight 4 28 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 28) : 0 ≤ alphaQ_s28_r5 c := by
    unfold alphaQ_s28_r5
    positivity
  have hprob : ∑ c, alphaQ_s28_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![328593829,77719457564,843903887656,77719469697,328591254] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999976600,500000023400,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 31 0 c : ℚ) / 1000000000000

private def jointExponent_s31_r0 (c : MME.ReleasedInterior.Split 31) : ℕ :=
  [12, 4, 1, 6, 6, 1, 4, 12].getD ((seed 4 31).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s31_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 31 => c.val 0)
        (fun c => (splitWeight 4 31 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 31 => (splitWeight 4 31 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 31) : 0 ≤ alphaQ_s31_r0 c := by
    unfold alphaQ_s31_r0
    positivity
  have hprob : ∑ c, alphaQ_s31_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![328608213,80540829368,838261138511,80540816609,328607299] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000026075,499999973925,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s31_r2 (c : MME.ReleasedInterior.Split 31) : ℚ :=
  (splitWeight 4 31 2 c : ℚ) / 1000000000000

private def jointExponent_s31_r2 (c : MME.ReleasedInterior.Split 31) : ℕ :=
  [12, 4, 1, 6, 6, 1, 4, 12].getD ((seed 4 31).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s31_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 31 => c.val 0)
        (fun c => (splitWeight 4 31 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 31 => (splitWeight 4 31 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 31) : 0 ≤ alphaQ_s31_r2 c := by
    unfold alphaQ_s31_r2
    positivity
  have hprob : ∑ c, alphaQ_s31_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![327425236,80464681937,838415806210,80464669594,327417023] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000034814,499999965186,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 31 3 c : ℚ) / 1000000000000

private def jointExponent_s31_r3 (c : MME.ReleasedInterior.Split 31) : ℕ :=
  [12, 4, 1, 6, 6, 1, 4, 12].getD ((seed 4 31).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s31_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 31 => c.val 0)
        (fun c => (splitWeight 4 31 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 31 => (splitWeight 4 31 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 31) : 0 ≤ alphaQ_s31_r3 c := by
    unfold alphaQ_s31_r3
    positivity
  have hprob : ∑ c, alphaQ_s31_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![324744696,77739083586,843872353096,77739081036,324737586] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000012900,499999987100,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s32_r1 (c : MME.ReleasedInterior.Split 32) : ℚ :=
  (splitWeight 4 32 1 c : ℚ) / 1000000000000

private def jointExponent_s32_r1 (c : MME.ReleasedInterior.Split 32) : ℕ :=
  [12, 5, 3, 5, 1, 5, 3, 5, 12].getD ((seed 4 32).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s32_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 32 => c.val 0)
        (fun c => (splitWeight 4 32 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 32 => (splitWeight 4 32 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 32) : 0 ≤ alphaQ_s32_r1 c := by
    unfold alphaQ_s32_r1
    positivity
  have hprob : ∑ c, alphaQ_s32_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![335740368,79184937440,840958644226,79184936073,335741893] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![180596394960,638807210606,180596394434,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s32_r3 (c : MME.ReleasedInterior.Split 32) : ℚ :=
  (splitWeight 4 32 3 c : ℚ) / 1000000000000

private def jointExponent_s32_r3 (c : MME.ReleasedInterior.Split 32) : ℕ :=
  [12, 5, 3, 5, 1, 5, 3, 5, 12].getD ((seed 4 32).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s32_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 32 => c.val 0)
        (fun c => (splitWeight 4 32 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 32 => (splitWeight 4 32 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 32) : 0 ≤ alphaQ_s32_r3 c := by
    unfold alphaQ_s32_r3
    positivity
  have hprob : ∑ c, alphaQ_s32_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![335773626,79188985427,840950482061,79188987108,335771778] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![180650538104,638698922032,180650539864,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s32_r3 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![12,4,0,4,12] ![12,4,0,4,12] ![3,1,3,40,40] jointExponent_s32_r3 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 32 => c.val 0)
        (fun c => (alphaQ_s32_r3 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s32_r3 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s32_r3, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s32_r4 (c : MME.ReleasedInterior.Split 32) : ℚ :=
  (splitWeight 4 32 4 c : ℚ) / 1000000000000

private def jointExponent_s32_r4 (c : MME.ReleasedInterior.Split 32) : ℕ :=
  [12, 5, 3, 5, 1, 5, 3, 5, 12].getD ((seed 4 32).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s32_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 32 => c.val 0)
        (fun c => (splitWeight 4 32 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 32 => (splitWeight 4 32 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 32) : 0 ≤ alphaQ_s32_r4 c := by
    unfold alphaQ_s32_r4
    positivity
  have hprob : ∑ c, alphaQ_s32_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![336116794,79863153005,839601460725,79863154392,336115084] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![181829286339,636341424618,181829289043,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s32_r5 (c : MME.ReleasedInterior.Split 32) : ℚ :=
  (splitWeight 4 32 5 c : ℚ) / 1000000000000

private def jointExponent_s32_r5 (c : MME.ReleasedInterior.Split 32) : ℕ :=
  [12, 5, 3, 5, 1, 5, 3, 5, 12].getD ((seed 4 32).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s32_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 32 => c.val 0)
        (fun c => (splitWeight 4 32 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 32 => (splitWeight 4 32 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 32) : 0 ≤ alphaQ_s32_r5 c := by
    unfold alphaQ_s32_r5
    positivity
  have hprob : ∑ c, alphaQ_s32_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![336168311,79865507605,839596648231,79865508547,336167306] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![181879880165,636240240626,181879879209,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  have hp : ∀ v, 0 < p v := by decide +kernel
  have hq : ∀ v, 0 < q v := by decide +kernel
  have hpmass : ∑ v, p v = 1 := by decide +kernel
  have hqmass : ∑ v, q v = 1 := by decide +kernel
  have h := mme_rational_coarse_penalty_certificate alphaQ_s32_r5 ha hprob 0 2
    (by decide) p q hp hq hpmass hqmass ![12,4,0,4,12] ![12,4,0,4,12] ![3,1,3,40,40] jointExponent_s32_r5 (2/5)
  have hc : ((2 / 5 : ℚ) : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 32 => c.val 0)
        (fun c => (alphaQ_s32_r5 c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alphaQ_s32_r5 c : ℝ)) := by
    apply h
    decide +kernel
  simpa only [alphaQ_s32_r5, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hc

private def alphaQ_s33_r0 (c : MME.ReleasedInterior.Split 33) : ℚ :=
  (splitWeight 4 33 0 c : ℚ) / 1000000000000

private def jointExponent_s33_r0 (c : MME.ReleasedInterior.Split 33) : ℕ :=
  [12, 6, 4, 1, 1, 4, 6, 12].getD ((seed 4 33).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s33_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 33 => c.val 0)
        (fun c => (splitWeight 4 33 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 33 => (splitWeight 4 33 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 33) : 0 ≤ alphaQ_s33_r0 c := by
    unfold alphaQ_s33_r0
    positivity
  have hprob : ∑ c, alphaQ_s33_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![328612996,80486760987,838369249366,80486764002,328612649] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999996129,500000003871,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s33_r1 (c : MME.ReleasedInterior.Split 33) : ℚ :=
  (splitWeight 4 33 1 c : ℚ) / 1000000000000

private def jointExponent_s33_r1 (c : MME.ReleasedInterior.Split 33) : ℕ :=
  [12, 6, 4, 1, 1, 4, 6, 12].getD ((seed 4 33).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s33_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 33 => c.val 0)
        (fun c => (splitWeight 4 33 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 33 => (splitWeight 4 33 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 33) : 0 ≤ alphaQ_s33_r1 c := by
    unfold alphaQ_s33_r1
    positivity
  have hprob : ∑ c, alphaQ_s33_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![326462765,77740333332,843866406849,77740335193,326461861] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000000569,499999999431,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s33_r2 (c : MME.ReleasedInterior.Split 33) : ℚ :=
  (splitWeight 4 33 2 c : ℚ) / 1000000000000

private def jointExponent_s33_r2 (c : MME.ReleasedInterior.Split 33) : ℕ :=
  [12, 6, 4, 1, 1, 4, 6, 12].getD ((seed 4 33).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s33_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 33 => c.val 0)
        (fun c => (splitWeight 4 33 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 33 => (splitWeight 4 33 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 33) : 0 ≤ alphaQ_s33_r2 c := by
    unfold alphaQ_s33_r2
    positivity
  have hprob : ∑ c, alphaQ_s33_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![329979501,80557612721,838224816418,80557611598,329979762] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000001854,499999998146,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s36_r0 (c : MME.ReleasedInterior.Split 36) : ℚ :=
  (splitWeight 4 36 0 c : ℚ) / 1000000000000

private def jointExponent_s36_r0 (c : MME.ReleasedInterior.Split 36) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 4 36).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s36_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 36 => c.val 0)
        (fun c => (splitWeight 4 36 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 36 => (splitWeight 4 36 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 36) : 0 ≤ alphaQ_s36_r0 c := by
    unfold alphaQ_s36_r0
    positivity
  have hprob : ∑ c, alphaQ_s36_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7369883011,492630115039,492630138763,7369863187] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999996163,500000003837,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 36 1 c : ℚ) / 1000000000000

private def jointExponent_s36_r1 (c : MME.ReleasedInterior.Split 36) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 4 36).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s36_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 36 => c.val 0)
        (fun c => (splitWeight 4 36 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 36 => (splitWeight 4 36 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 36) : 0 ≤ alphaQ_s36_r1 c := by
    unfold alphaQ_s36_r1
    positivity
  have hprob : ∑ c, alphaQ_s36_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7328659036,492671321379,492671377654,7328641931] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000017215,499999982785,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 36 2 c : ℚ) / 1000000000000

private def jointExponent_s36_r2 (c : MME.ReleasedInterior.Split 36) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 4 36).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s36_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 36 => c.val 0)
        (fun c => (splitWeight 4 36 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 36 => (splitWeight 4 36 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 36) : 0 ≤ alphaQ_s36_r2 c := by
    unfold alphaQ_s36_r2
    positivity
  have hprob : ∑ c, alphaQ_s36_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7354517683,492645482896,492645493311,7354506110] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499999997574,500000002426,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 36 3 c : ℚ) / 1000000000000

private def jointExponent_s36_r3 (c : MME.ReleasedInterior.Split 36) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 4 36).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s36_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 36 => c.val 0)
        (fun c => (splitWeight 4 36 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 36 => (splitWeight 4 36 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 36) : 0 ≤ alphaQ_s36_r3 c := by
    unfold alphaQ_s36_r3
    positivity
  have hprob : ∑ c, alphaQ_s36_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7256726067,492743283075,492743174357,7256816501] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000025001,499999974999,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 36 4 c : ℚ) / 1000000000000

private def jointExponent_s36_r4 (c : MME.ReleasedInterior.Split 36) : ℕ :=
  [7, 2, 3, 3, 2, 7].getD ((seed 4 36).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s36_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 36 => c.val 0)
        (fun c => (splitWeight 4 36 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 36 => (splitWeight 4 36 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 36) : 0 ≤ alphaQ_s36_r4 c := by
    unfold alphaQ_s36_r4
    positivity
  have hprob : ∑ c, alphaQ_s36_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7317727920,492682248444,492682318999,7317704637] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000017635,499999982365,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s37_r0 (c : MME.ReleasedInterior.Split 37) : ℚ :=
  (splitWeight 4 37 0 c : ℚ) / 1000000000000

private def jointExponent_s37_r0 (c : MME.ReleasedInterior.Split 37) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 4 37).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s37_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 37 => c.val 0)
        (fun c => (splitWeight 4 37 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 37 => (splitWeight 4 37 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 37) : 0 ≤ alphaQ_s37_r0 c := by
    unfold alphaQ_s37_r0
    positivity
  have hprob : ∑ c, alphaQ_s37_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7346669028,492653348399,492653178414,7346804159] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000032832,499999967168,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 37 1 c : ℚ) / 1000000000000

private def jointExponent_s37_r1 (c : MME.ReleasedInterior.Split 37) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 4 37).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s37_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 37 => c.val 0)
        (fun c => (splitWeight 4 37 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 37 => (splitWeight 4 37 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 37) : 0 ≤ alphaQ_s37_r1 c := by
    unfold alphaQ_s37_r1
    positivity
  have hprob : ∑ c, alphaQ_s37_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7250705767,492749321335,492749057787,7250915111] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000045859,499999954141,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 37 2 c : ℚ) / 1000000000000

private def jointExponent_s37_r2 (c : MME.ReleasedInterior.Split 37) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 4 37).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s37_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 37 => c.val 0)
        (fun c => (splitWeight 4 37 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 37 => (splitWeight 4 37 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 37) : 0 ≤ alphaQ_s37_r2 c := by
    unfold alphaQ_s37_r2
    positivity
  have hprob : ∑ c, alphaQ_s37_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7363602946,492636418389,492636225365,7363753300] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000034526,499999965474,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 37 3 c : ℚ) / 1000000000000

private def jointExponent_s37_r3 (c : MME.ReleasedInterior.Split 37) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 4 37).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s37_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 37 => c.val 0)
        (fun c => (splitWeight 4 37 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 37 => (splitWeight 4 37 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 37) : 0 ≤ alphaQ_s37_r3 c := by
    unfold alphaQ_s37_r3
    positivity
  have hprob : ∑ c, alphaQ_s37_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7325217014,492674800057,492674615646,7325367283] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000039524,499999960476,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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

private def alphaQ_s37_r5 (c : MME.ReleasedInterior.Split 37) : ℚ :=
  (splitWeight 4 37 5 c : ℚ) / 1000000000000

private def jointExponent_s37_r5 (c : MME.ReleasedInterior.Split 37) : ℕ :=
  [7, 3, 2, 2, 3, 7].getD ((seed 4 37).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s37_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 37 => c.val 0)
        (fun c => (splitWeight 4 37 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 37 => (splitWeight 4 37 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 37) : 0 ≤ alphaQ_s37_r5 c := by
    unfold alphaQ_s37_r5
    positivity
  have hprob : ∑ c, alphaQ_s37_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![0,7308651992,492687494131,492691490839,7312363038] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500008327671,499991672329,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 40 0 c : ℚ) / 1000000000000

private def jointExponent_s40_r0 (c : MME.ReleasedInterior.Split 40) : ℕ :=
  [3, 1, 1, 3].getD ((seed 4 40).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s40_r0 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 40 => c.val 0)
        (fun c => (splitWeight 4 40 0 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 40 => (splitWeight 4 40 0 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 40) : 0 ≤ alphaQ_s40_r0 c := by
    unfold alphaQ_s40_r0
    positivity
  have hprob : ∑ c, alphaQ_s40_r0 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499948359345,500051640655,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500026313304,499973686696,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 40 1 c : ℚ) / 1000000000000

private def jointExponent_s40_r1 (c : MME.ReleasedInterior.Split 40) : ℕ :=
  [3, 1, 1, 3].getD ((seed 4 40).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s40_r1 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 40 => c.val 0)
        (fun c => (splitWeight 4 40 1 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 40 => (splitWeight 4 40 1 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 40) : 0 ≤ alphaQ_s40_r1 c := by
    unfold alphaQ_s40_r1
    positivity
  have hprob : ∑ c, alphaQ_s40_r1 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499985523190,500014476810,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500004240635,499995759365,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 40 2 c : ℚ) / 1000000000000

private def jointExponent_s40_r2 (c : MME.ReleasedInterior.Split 40) : ℕ :=
  [3, 1, 1, 3].getD ((seed 4 40).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s40_r2 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 40 => c.val 0)
        (fun c => (splitWeight 4 40 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 40 => (splitWeight 4 40 2 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 40) : 0 ≤ alphaQ_s40_r2 c := by
    unfold alphaQ_s40_r2
    positivity
  have hprob : ∑ c, alphaQ_s40_r2 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499948245810,500051754190,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500026376004,499973623996,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 40 3 c : ℚ) / 1000000000000

private def jointExponent_s40_r3 (c : MME.ReleasedInterior.Split 40) : ℕ :=
  [3, 1, 1, 3].getD ((seed 4 40).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s40_r3 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 40 => c.val 0)
        (fun c => (splitWeight 4 40 3 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 40 => (splitWeight 4 40 3 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 40) : 0 ≤ alphaQ_s40_r3 c := by
    unfold alphaQ_s40_r3
    positivity
  have hprob : ∑ c, alphaQ_s40_r3 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![500012746616,499987253384,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![499993496467,500006503533,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 40 4 c : ℚ) / 1000000000000

private def jointExponent_s40_r4 (c : MME.ReleasedInterior.Split 40) : ℕ :=
  [3, 1, 1, 3].getD ((seed 4 40).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s40_r4 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 40 => c.val 0)
        (fun c => (splitWeight 4 40 4 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 40 => (splitWeight 4 40 4 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 40) : 0 ≤ alphaQ_s40_r4 c := by
    unfold alphaQ_s40_r4
    positivity
  have hprob : ∑ c, alphaQ_s40_r4 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999755940,500000244060,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000130672,499999869328,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
  (splitWeight 4 40 5 c : ℚ) / 1000000000000

private def jointExponent_s40_r5 (c : MME.ReleasedInterior.Split 40) : ℕ :=
  [3, 1, 1, 3].getD ((seed 4 40).splits.idxOf (sourceShape 4 c)) 0

private theorem region_s40_r5 :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 40 => c.val 0)
        (fun c => (splitWeight 4 40 5 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 40 => (splitWeight 4 40 5 c : ℝ) / 1000000000000) := by
  have ha (c : MME.ReleasedInterior.Split 40) : 0 ≤ alphaQ_s40_r5 c := by
    unfold alphaQ_s40_r5
    positivity
  have hprob : ∑ c, alphaQ_s40_r5 c = 1 := by decide +kernel
  let p : Fin 5 → ℚ := fun v => ((![499999760796,500000239204,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
  let q : Fin 5 → ℚ := fun v => ((![500000127046,499999872954,0,0,0] : Fin 5 → ℕ) v + 1 : ℚ) / 1000000000005
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
    (s : Fin 45) (r : Fin 6) (hi : (seed 4 s).boundary = [])
    (hn : 0 < (seed 4 s).region.getD r.val 0) :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split s => c.val 0)
        (fun c => (splitWeight 4 s r c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split s => (splitWeight 4 s r c : ℝ) / 1000000000000) := by
  fin_cases s
  · exact False.elim ((by decide +kernel : (seed 4 0).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 4 1).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 4 2).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 4 3).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 4 4).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 4 5).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 4 6).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 4 7).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 4 8).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 4 9).boundary ≠ []) hi)
  · fin_cases r
    · exact region_s10_r0
    · exact region_s10_r1
    · exact region_s10_r2
    · exact region_s10_r3
    · exact region_s10_r4
    · exact region_s10_r5
  · fin_cases r
    · exact region_s11_r0
    · exact region_s11_r1
    · have hz : (seed 4 11).region.getD 2 0 = 0 := by decide +kernel
      change 0 < (seed 4 11).region.getD 2 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 4 11).region.getD 3 0 = 0 := by decide +kernel
      change 0 < (seed 4 11).region.getD 3 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s11_r4
    · have hz : (seed 4 11).region.getD 5 0 = 0 := by decide +kernel
      change 0 < (seed 4 11).region.getD 5 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
  · fin_cases r
    · exact region_s12_r0
    · exact region_s12_r1
    · have hz : (seed 4 12).region.getD 2 0 = 0 := by decide +kernel
      change 0 < (seed 4 12).region.getD 2 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 4 12).region.getD 3 0 = 0 := by decide +kernel
      change 0 < (seed 4 12).region.getD 3 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s12_r4
    · have hz : (seed 4 12).region.getD 5 0 = 0 := by decide +kernel
      change 0 < (seed 4 12).region.getD 5 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
  · fin_cases r
    · have hz : (seed 4 13).region.getD 0 0 = 0 := by decide +kernel
      change 0 < (seed 4 13).region.getD 0 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 4 13).region.getD 1 0 = 0 := by decide +kernel
      change 0 < (seed 4 13).region.getD 1 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s13_r2
    · exact region_s13_r3
    · have hz : (seed 4 13).region.getD 4 0 = 0 := by decide +kernel
      change 0 < (seed 4 13).region.getD 4 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s13_r5
  · fin_cases r
    · have hz : (seed 4 14).region.getD 0 0 = 0 := by decide +kernel
      change 0 < (seed 4 14).region.getD 0 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s14_r1
    · exact region_s14_r2
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
  · exact False.elim ((by decide +kernel : (seed 4 16).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 4 17).boundary ≠ []) hi)
  · fin_cases r
    · have hz : (seed 4 18).region.getD 0 0 = 0 := by decide +kernel
      change 0 < (seed 4 18).region.getD 0 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s18_r1
    · have hz : (seed 4 18).region.getD 2 0 = 0 := by decide +kernel
      change 0 < (seed 4 18).region.getD 2 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 4 18).region.getD 3 0 = 0 := by decide +kernel
      change 0 < (seed 4 18).region.getD 3 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s18_r4
    · exact region_s18_r5
  · fin_cases r
    · exact region_s19_r0
    · exact region_s19_r1
    · have hz : (seed 4 19).region.getD 2 0 = 0 := by decide +kernel
      change 0 < (seed 4 19).region.getD 2 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 4 19).region.getD 3 0 = 0 := by decide +kernel
      change 0 < (seed 4 19).region.getD 3 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s19_r4
    · exact region_s19_r5
  · fin_cases r
    · exact region_s20_r0
    · exact region_s20_r1
    · exact region_s20_r2
    · exact region_s20_r3
    · have hz : (seed 4 20).region.getD 4 0 = 0 := by decide +kernel
      change 0 < (seed 4 20).region.getD 4 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 4 20).region.getD 5 0 = 0 := by decide +kernel
      change 0 < (seed 4 20).region.getD 5 0 at hn
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
    · have hz : (seed 4 22).region.getD 1 0 = 0 := by decide +kernel
      change 0 < (seed 4 22).region.getD 1 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s22_r2
    · exact region_s22_r3
    · exact region_s22_r4
    · exact region_s22_r5
  · exact False.elim ((by decide +kernel : (seed 4 23).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 4 24).boundary ≠ []) hi)
  · fin_cases r
    · have hz : (seed 4 25).region.getD 0 0 = 0 := by decide +kernel
      change 0 < (seed 4 25).region.getD 0 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s25_r1
    · have hz : (seed 4 25).region.getD 2 0 = 0 := by decide +kernel
      change 0 < (seed 4 25).region.getD 2 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 4 25).region.getD 3 0 = 0 := by decide +kernel
      change 0 < (seed 4 25).region.getD 3 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s25_r4
    · exact region_s25_r5
  · fin_cases r
    · have hz : (seed 4 26).region.getD 0 0 = 0 := by decide +kernel
      change 0 < (seed 4 26).region.getD 0 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 4 26).region.getD 1 0 = 0 := by decide +kernel
      change 0 < (seed 4 26).region.getD 1 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s26_r2
    · exact region_s26_r3
    · exact region_s26_r4
    · exact region_s26_r5
  · fin_cases r
    · exact region_s27_r0
    · exact region_s27_r1
    · have hz : (seed 4 27).region.getD 2 0 = 0 := by decide +kernel
      change 0 < (seed 4 27).region.getD 2 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 4 27).region.getD 3 0 = 0 := by decide +kernel
      change 0 < (seed 4 27).region.getD 3 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s27_r4
    · exact region_s27_r5
  · fin_cases r
    · have hz : (seed 4 28).region.getD 0 0 = 0 := by decide +kernel
      change 0 < (seed 4 28).region.getD 0 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 4 28).region.getD 1 0 = 0 := by decide +kernel
      change 0 < (seed 4 28).region.getD 1 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 4 28).region.getD 2 0 = 0 := by decide +kernel
      change 0 < (seed 4 28).region.getD 2 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s28_r3
    · exact region_s28_r4
    · exact region_s28_r5
  · exact False.elim ((by decide +kernel : (seed 4 29).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 4 30).boundary ≠ []) hi)
  · fin_cases r
    · exact region_s31_r0
    · have hz : (seed 4 31).region.getD 1 0 = 0 := by decide +kernel
      change 0 < (seed 4 31).region.getD 1 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s31_r2
    · exact region_s31_r3
    · have hz : (seed 4 31).region.getD 4 0 = 0 := by decide +kernel
      change 0 < (seed 4 31).region.getD 4 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 4 31).region.getD 5 0 = 0 := by decide +kernel
      change 0 < (seed 4 31).region.getD 5 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
  · fin_cases r
    · have hz : (seed 4 32).region.getD 0 0 = 0 := by decide +kernel
      change 0 < (seed 4 32).region.getD 0 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s32_r1
    · have hz : (seed 4 32).region.getD 2 0 = 0 := by decide +kernel
      change 0 < (seed 4 32).region.getD 2 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s32_r3
    · exact region_s32_r4
    · exact region_s32_r5
  · fin_cases r
    · exact region_s33_r0
    · exact region_s33_r1
    · exact region_s33_r2
    · have hz : (seed 4 33).region.getD 3 0 = 0 := by decide +kernel
      change 0 < (seed 4 33).region.getD 3 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 4 33).region.getD 4 0 = 0 := by decide +kernel
      change 0 < (seed 4 33).region.getD 4 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · have hz : (seed 4 33).region.getD 5 0 = 0 := by decide +kernel
      change 0 < (seed 4 33).region.getD 5 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
  · exact False.elim ((by decide +kernel : (seed 4 34).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 4 35).boundary ≠ []) hi)
  · fin_cases r
    · exact region_s36_r0
    · exact region_s36_r1
    · exact region_s36_r2
    · exact region_s36_r3
    · exact region_s36_r4
    · have hz : (seed 4 36).region.getD 5 0 = 0 := by decide +kernel
      change 0 < (seed 4 36).region.getD 5 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
  · fin_cases r
    · exact region_s37_r0
    · exact region_s37_r1
    · exact region_s37_r2
    · exact region_s37_r3
    · have hz : (seed 4 37).region.getD 4 0 = 0 := by decide +kernel
      change 0 < (seed 4 37).region.getD 4 0 at hn
      rw [hz] at hn
      exact False.elim ((lt_irrefl 0) hn)
    · exact region_s37_r5
  · exact False.elim ((by decide +kernel : (seed 4 38).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 4 39).boundary ≠ []) hi)
  · fin_cases r
    · exact region_s40_r0
    · exact region_s40_r1
    · exact region_s40_r2
    · exact region_s40_r3
    · exact region_s40_r4
    · exact region_s40_r5
  · exact False.elim ((by decide +kernel : (seed 4 41).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 4 42).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 4 43).boundary ≠ []) hi)
  · exact False.elim ((by decide +kernel : (seed 4 44).boundary ≠ []) hi)


#print axioms solution
