-- Prove2me | Theorems.Thm_mme_entropy_penalty_upper_stability
-- name    : mme_entropy_penalty_upper_stability
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T08:49:16.364205+00:00
-- url     : https://prove2.me/theorems/f71e57ac-b52f-4e28-ba3f-cf8678bd7336
-- title:
--   Upper stability of the compatible-marginal maximum-entropy penalty
-- statement:
--   Let alpha be a probability distribution on the finite split alphabet and let delta>0. There is epsilon>0 such that every probability distribution beta within epsilon of alpha in every coordinate satisfies log(2) P(beta) <= log(2) P(alpha)+delta, where P is the maximum-entropy penalty in bits. Zero entries are permitted. The tolerance is existential.
-- source:
--   More Asymmetry Theorem 5.3 global stage: https://arxiv.org/html/2404.16349v2#S5. Generic finite entropy and tolerance estimates; not a completed numerical exponent certificate.

import Definitions.Def_mme_global_CW_real_entropy_profiles
import Definitions.Def_mme_global_CW_joint_start_data
open BigOperators MME MME.TensorObj MME.ProfiledCW MME.GlobalCW MME.RegionRate MME.RegionRealization MME.RecursiveYZ MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
universe u

theorem mme_entropy_penalty_upper_stability {degree : ℕ} {bounds : Fin 3 → ℕ}
    (alpha : Split degree bounds → ℝ) (hpos : ∀ c, 0 ≤ alpha c)
    (hmass : ∑ c, alpha c = 1) (delta : ℝ) (hdelta : 0 < delta) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ beta : Split degree bounds → ℝ,
      (∀ c, 0 ≤ beta c) → (∑ c, beta c = 1) →
      (∀ c, |beta c - alpha c| ≤ eps) →
      Real.log 2 * entropyPenalty beta ≤ Real.log 2 * entropyPenalty alpha + delta  := by
  sorry
