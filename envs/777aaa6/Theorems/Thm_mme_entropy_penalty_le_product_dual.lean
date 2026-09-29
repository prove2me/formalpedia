-- Prove2me | Theorems.Thm_mme_entropy_penalty_le_product_dual
-- name    : mme_entropy_penalty_le_product_dual
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T06:45:46.679886+00:00
-- url     : https://prove2.me/theorems/7f84209a-7773-4b21-b2f8-20a09cf21679
-- title:
--   Product weights certify an upper bound on the entropy penalty
-- statement:
--   A feasible positive product of coordinate weights bounds the maximum-entropy penalty in natural-log units. This gives a certificate interface without requiring an exact entropy maximizer. Numerical feasibility and logarithm bounds for released recipes remain separate obligations. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Theorems.Thm_mme_same_marginal_entropy_le_product_dual
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
open scoped BigOperators
open MME.RegionRate MME.RecursiveThinSplit

theorem mme_entropy_penalty_le_product_dual
    {half : ℕ} {parent : Fin 3 → ℕ} (alpha : Split half parent → ℝ)
    (ha : ∀ c, 0 ≤ alpha c) (hprob : ∑ c, alpha c = 1)
    (weights : Fin 3 → Fin (half + 1) → ℝ)
    (hpos : ∀ i j, 0 < weights i j)
    (hmass : ∑ c : Split half parent, ∏ i, weights i (c.val i) ≤ 1) :
    Real.log 2 * entropyPenalty alpha ≤
      -(∑ i, ∑ j, mme_modern_marginal (fun c : Split half parent => c.val i) alpha j *
        Real.log (weights i j)) - entropy alpha := by sorry
