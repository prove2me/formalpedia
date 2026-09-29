-- Prove2me | Theorems.Thm_mme_entropy_penalty_of_positive_reference
-- name    : mme_entropy_penalty_of_positive_reference
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T11:56:26.081984+00:00
-- url     : https://prove2.me/theorems/7bf34534-1792-4359-84bb-1617fb68d4d6
-- title:
--   Bound the maximum-entropy penalty by a positive reference distribution
-- statement:
--   For a normalized nonnegative coarse profile alpha and a positive normalized reference q, if every same-marginal distribution has the same q-log moment as alpha, the natural-log entropy penalty is at most cross-entropy(alpha,q) minus entropy(alpha).
-- source:
--   Numerical global X-rate certification for the exact ReleasedGlobal candidate from More Asymmetry, https://arxiv.org/html/2404.16349v2#S5 . Y/Z numerical rates and whole-interface recursive continuation remain separate.

import Definitions.Def_mme_released_global_x_certificate
open BigOperators MME MME.ReleasedGlobal MME.ReleasedGlobalNumeric MME.MoreAsymmetryExactSeed MME.RegionRate MME.RecursiveThinSplit MME.GlobalCW
open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 3000

theorem mme_entropy_penalty_of_positive_reference {degree : ℕ} {bounds : Fin 3 → ℕ}
    (alpha q : Split degree bounds → ℝ)
    (hp : ∀ c, 0 ≤ alpha c) (hm : ∑ c, alpha c = 1)
    (hq : ∀ c, 0 < q c) (hqm : ∑ c, q c = 1)
    (hmoment : ∀ rho ∈ SameMarginalDistributions alpha,
      (∑ c, rho c * Real.log (q c)) = ∑ c, alpha c * Real.log (q c)) :
    Real.log 2 * entropyPenalty alpha ≤
      -(∑ c, alpha c * Real.log (q c)) - entropy alpha := by
  sorry
