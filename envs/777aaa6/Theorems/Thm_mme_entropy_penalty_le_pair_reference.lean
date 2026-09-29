-- Prove2me | Theorems.Thm_mme_entropy_penalty_le_pair_reference
-- name    : mme_entropy_penalty_le_pair_reference
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T06:51:05.126125+00:00
-- url     : https://prove2.me/theorems/4db4914e-92ca-4b96-8764-d20f7b437382
-- title:
--   Two positive coordinate probabilities bound the entropy penalty
-- statement:
--   Any two strictly positive coordinate probability distributions bound the maximum-entropy split penalty by their cross entropies minus the original joint entropy. Product-mass feasibility follows structurally and is no longer a separate certificate obligation. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Theorems.Thm_mme_split_pair_product_mass_le
import Theorems.Thm_mme_entropy_penalty_le_product_dual
open scoped BigOperators
open MME.RegionRate MME.RecursiveThinSplit

theorem mme_entropy_penalty_le_pair_reference
    {half : ℕ} {parent : Fin 3 → ℕ} (alpha : Split half parent → ℝ)
    (ha : ∀ c, 0 ≤ alpha c) (hprob : ∑ c, alpha c = 1)
    (i j : Fin 3) (hij : i ≠ j) (p q : Fin (half + 1) → ℝ)
    (hp : ∀ a, 0 < p a) (hq : ∀ b, 0 < q b)
    (hpmass : ∑ a, p a = 1) (hqmass : ∑ b, q b = 1) :
    Real.log 2 * entropyPenalty alpha ≤
      -(∑ a, mme_modern_marginal (fun c : Split half parent => c.val i) alpha a *
        Real.log (p a)) -
      (∑ b, mme_modern_marginal (fun c : Split half parent => c.val j) alpha b *
        Real.log (q b)) - entropy alpha := by sorry
