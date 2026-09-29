-- Prove2me | solution 1 for mme_entropy_penalty_le_product_dual
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T06:47:52.310213+00:00
-- url     : https://prove2.me/submissions/961b3729-6cfb-4f90-bd55-88b817423e6b

import Theorems.Thm_mme_same_marginal_entropy_le_product_dual
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open scoped BigOperators
open MME.RegionRate MME.RecursiveThinSplit

/-- A finite product-dual certificate bounds the maximum-entropy penalty in
natural-log units, without solving the entropy maximization problem. -/
theorem solution
    {half : ℕ} {parent : Fin 3 → ℕ} (alpha : Split half parent → ℝ)
    (ha : ∀ c, 0 ≤ alpha c) (hprob : ∑ c, alpha c = 1)
    (weights : Fin 3 → Fin (half + 1) → ℝ)
    (hpos : ∀ i j, 0 < weights i j)
    (hmass : ∑ c : Split half parent, ∏ i, weights i (c.val i) ≤ 1) :
    Real.log 2 * entropyPenalty alpha ≤
      -(∑ i, ∑ j, mme_modern_marginal (fun c : Split half parent => c.val i) alpha j *
        Real.log (weights i j)) - entropy alpha := by
  let bound := -(∑ i, ∑ j,
    mme_modern_marginal (fun c : Split half parent => c.val i) alpha j *
      Real.log (weights i j))
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnon : (mme_modern_entropyBits '' SameMarginalDistributions alpha).Nonempty :=
    ⟨_, alpha, ⟨ha, hprob, fun _ _ => rfl⟩, rfl⟩
  have hsup : sSup (mme_modern_entropyBits '' SameMarginalDistributions alpha) ≤
      bound / Real.log 2 := by
    apply csSup_le hnon
    rintro _ ⟨rho, hrho, rfl⟩
    exact div_le_div_of_nonneg_right
      (mme_same_marginal_entropy_le_product_dual alpha weights hpos hmass rho hrho) hl.le
  have hpen : entropyPenalty alpha ≤ bound / Real.log 2 - mme_modern_entropyBits alpha :=
    sub_le_sub_right hsup _
  calc
    _ ≤ Real.log 2 * (bound / Real.log 2 - mme_modern_entropyBits alpha) :=
      mul_le_mul_of_nonneg_left hpen hl.le
    _ = bound - entropy alpha := by
      unfold mme_modern_entropyBits entropy
      field_simp
    _ = _ := rfl


#print axioms solution
