-- Prove2me | Theorems.Thm_mme_entropy_penalty_le_smoothed_counts
-- name    : mme_entropy_penalty_le_smoothed_counts
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T07:00:29.749813+00:00
-- url     : https://prove2.me/theorems/4b61d755-7319-4f3b-9315-8f1ab7e2f78f
-- title:
--   Smoothed integer counts certify entropy-penalty bounds
-- statement:
--   Adding one to every entry of each of two nonnegative integer count vectors and normalizing by the total plus the alphabet size gives a valid entropy-penalty bound. Zero entries and zero total are allowed. Only the two exact count-total identities are required; numerical logarithm bounds remain separate. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Theorems.Thm_mme_entropy_penalty_le_pair_reference
open scoped BigOperators
open MME.RegionRate MME.RecursiveThinSplit

theorem mme_entropy_penalty_le_smoothed_counts
    {half : ℕ} {parent : Fin 3 → ℕ} (alpha : Split half parent → ℝ)
    (ha : ∀ c, 0 ≤ alpha c) (hprob : ∑ c, alpha c = 1)
    (i j : Fin 3) (hij : i ≠ j) (D : ℕ)
    (a b : Fin (half + 1) → ℕ) (haD : ∑ v, a v = D) (hbD : ∑ v, b v = D) :
    Real.log 2 * entropyPenalty alpha ≤
      -(∑ v, mme_modern_marginal (fun c : Split half parent => c.val i) alpha v *
        Real.log (((a v : ℝ) + 1) / ((D : ℝ) + (half + 1)))) -
      (∑ v, mme_modern_marginal (fun c : Split half parent => c.val j) alpha v *
        Real.log (((b v : ℝ) + 1) / ((D : ℝ) + (half + 1)))) - entropy alpha := by sorry
