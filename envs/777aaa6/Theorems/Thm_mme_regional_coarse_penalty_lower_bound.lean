-- Prove2me | Theorems.Thm_mme_regional_coarse_penalty_lower_bound
-- name    : mme_regional_coarse_penalty_lower_bound
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T07:00:46.781053+00:00
-- url     : https://prove2.me/theorems/ae1b6472-9bb0-4cc6-b9ab-49a0981fa66e
-- title:
--   Normalized entropy margins give a weighted coarse-minus-penalty bound
-- statement:
--   If each nonempty region has normalized coarse entropy minus penalty at least b and split counts exhaust region masses, the total coarse potential minus penalty potential is at least b times total mass. Empty regions are allowed. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Theorems.Thm_mme_regional_mass_entropy_algebra
import Definitions.Def_mme_regional_split_entropy_data
open scoped BigOperators
open MME.RegionRate MME.RecursiveThinSplit

theorem mme_regional_coarse_penalty_lower_bound
    {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (n : Fin R → ℕ) (m : ∀ r, Split half (parent r) → ℕ)
    (hm : ∀ r, ∑ c, m r c = n r) (b : ℝ)
    (hb : ∀ r, 0 < n r → b ≤
      entropy (mme_modern_marginal (fun c : Split half (parent r) => c.val 0)
        (fun c => (m r c : ℝ) / n r)) -
      Real.log 2 * entropyPenalty (fun c => (m r c : ℝ) / n r)) :
    b * (∑ r, n r : ℕ) ≤ coarsePotential m 0 - penaltyPotential n m := by sorry
