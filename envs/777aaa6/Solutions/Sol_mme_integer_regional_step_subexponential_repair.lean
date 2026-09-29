-- Prove2me | solution 1 for mme_integer_regional_step_subexponential_repair
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T17:36:08.113536+00:00
-- url     : https://prove2.me/submissions/603b9a4f-010e-4e41-9b91-157aa68c60c4

import Definitions.Def_mme_integer_regional_CW_recipe
import Theorems.Thm_mme_recursive_region_word_capacity_bound
import Theorems.Thm_mme_square_scale_logarithmic_repair_cost

open BigOperators MME MME.ProfiledCW MME.RegionRealization MME.RecursiveYZ
set_option autoImplicit false

theorem solution (C : ℕ) (delta : ℝ) (hdelta : 0 < delta) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ {ell M : ℕ} {P : Predicate M}
      (D : IntegerStep ell M P), D.repairScale = k → M ≤ C * k ^ 2 →
      Real.log ((8 : ℝ) ^ D.repairExponent) < delta * (k : ℝ) ^ 2 := by
  obtain ⟨K,hK⟩ := mme_square_scale_logarithmic_repair_cost (3 * C) delta hdelta
  refine ⟨K,fun k hk ell M P D hd hM ↦ ?_⟩
  have hp : Fintype.card (Position D.n) = D.L := by
    simpa only [Fintype.card_fin] using (Fintype.card_congr D.positions).symm
  have hcap := mme_recursive_region_word_capacity_bound ell (fullCell D.total D.reference)
    (fun c i ↦ (c.2.val i).val) D.mu
  rw [hp,D.length] at hcap
  have hbound : D.capacity ≤ 7 ^ ((3 * C) * k ^ 2) := hcap.trans
    (Nat.pow_le_pow_right (by omega) (by nlinarith))
  have h := (hK k hk D.capacity hbound).2.2
  simpa only [IntegerStep.repairExponent,hd] using h
