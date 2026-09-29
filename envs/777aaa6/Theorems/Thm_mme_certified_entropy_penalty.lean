-- Prove2me | Theorems.Thm_mme_certified_entropy_penalty
-- name    : mme_certified_entropy_penalty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-22T21:22:15.969651+00:00
-- url     : https://prove2.me/theorems/396c571c-80bf-469b-887e-9df4b8682802
-- title:
--   Explicit upper bound on the recursive entropy penalty from coordinatewise weights
-- statement:
--   An explicit upper bound on the recursive maximum-entropy penalty, from per-coordinate weights.
--
--   The penalty compares a split distribution with the largest entropy achievable by any distribution
--   with the same coordinate marginals, so bounding it above means bounding that maximum. The Gibbs
--   dual does this: any positive reference distribution whose logarithm is a sum of per-coordinate
--   terms has the same expectation under every distribution with those marginals, and therefore
--   certifies a bound.
--
--   Choosing the reference to be proportional to a product of per-coordinate smooth values
--   `2^a 3^b 5^c 7^d` makes that bound computable: the penalty is at most the logarithm of the total
--   reference mass, minus the reference log-moment of the distribution, minus its entropy. The first
--   part records the underlying fact that a coordinatewise weight only sees that coordinate's marginal.
-- source:
--   Duan-Wu-Zhou fourth-power recursive construction (https://arxiv.org/html/2210.10173v5, section 7) combined with the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6). Exact finite or asymptotic-rate statement as written; no exponent claim.

import Mathlib
import Definitions.Def_mme_certified_entropy_reference
import Definitions.Def_mme_recursive_thin_split_data
import Definitions.Def_mme_modern_entropy_data
import Theorems.Thm_mme_entropy_penalty_of_positive_reference
open BigOperators MME MME.RegionRate MME.RecursiveThinSplit MME.Cert
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem mme_certified_entropy_penalty :
    (∀ {half : ℕ} {parent : Fin 3 → ℕ} (p : RecursiveThinSplit.Split half parent → ℝ)
      (i : Fin 3) (L : Fin (half + 1) → ℝ),
      ∑ c, p c * L (c.val i) =
        ∑ j, L j * mme_modern_marginal
          (fun a : RecursiveThinSplit.Split half parent ↦ a.val i) p j) ∧
    ∀ {half : ℕ} {parent : Fin 3 → ℕ} (alpha : RecursiveThinSplit.Split half parent → ℝ),
      (∀ c, 0 ≤ alpha c) → ∑ c, alpha c = 1 →
      ∀ E : Fin 3 → Fin (half + 1) → (Fin 4 → ℤ),
      Real.log 2 * entropyPenalty alpha ≤
        Real.log (∑ c : RecursiveThinSplit.Split half parent,
            qval (fun k ↦ ∑ i, E i (c.val i) k)) -
          (∑ c, alpha c * ∑ i, Real.log (qval (E i (c.val i)))) - entropy alpha := by sorry
