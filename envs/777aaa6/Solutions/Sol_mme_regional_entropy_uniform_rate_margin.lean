-- Prove2me | solution 1 for mme_regional_entropy_uniform_rate_margin
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T07:43:16.016442+00:00
-- url     : https://prove2.me/submissions/36230621-e5ae-441e-8e65-c68e6a623d79

import Theorems.Thm_mme_regional_entropy_uniform_modulus

open MME.RegionRate

/-- A strict rate margin survives the entropy-continuity error for every
sufficiently small positive tolerance, uniformly in any larger rate. -/
theorem solution
    {W : Type*} [Fintype W] (mass lower loss : ℝ)
    (hmass : 0 < mass) (hmargin : 2 * loss < lower) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ e : ℝ, 0 ≤ e → e ≤ eps →
      ∀ rate : ℝ, lower ≤ rate →
        2 * loss < rate - mass * entropyModulus W e := by
  let delta := (lower - 2 * loss) / (2 * mass)
  have hdelta : 0 < delta := div_pos (sub_pos.mpr hmargin) (by positivity)
  obtain ⟨eps, heps, hsmall⟩ :=
    (mme_regional_entropy_uniform_modulus (W := W)).2.2 delta hdelta
  refine ⟨eps, heps, fun e he heps rate hrate => ?_⟩
  have herror := mul_le_mul_of_nonneg_left (hsmall e he heps) hmass.le
  have hid : mass * delta = (lower - 2 * loss) / 2 := by
    dsimp [delta]
    field_simp
  rw [hid] at herror
  linarith


#print axioms solution
