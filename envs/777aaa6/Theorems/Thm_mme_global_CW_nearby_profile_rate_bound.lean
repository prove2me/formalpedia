-- Prove2me | Theorems.Thm_mme_global_CW_nearby_profile_rate_bound
-- name    : mme_global_CW_nearby_profile_rate_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T08:49:58.702965+00:00
-- url     : https://prove2.me/theorems/e1c608b1-8d83-45bd-92be-5171bef28d00
-- title:
--   Uniform lower stability of the pooled global profile rate
-- statement:
--   Fix normalized joint distributions and real joint cell-word profiles on finitely many regions. For every delta>0 there is one positive coordinate tolerance such that every nearby profile with normalized nonnegative joint distributions has pooled global rate at least the reference rate minus delta times the sum of region weights. This holds simultaneously for every choice of nonnegative region weights. The minimum is taken after summing the three rates over regions.
-- source:
--   More Asymmetry Theorem 5.3 global stage: https://arxiv.org/html/2404.16349v2#S5. Generic finite entropy and tolerance estimates; not a completed numerical exponent certificate.

import Definitions.Def_mme_global_CW_real_entropy_profiles
import Definitions.Def_mme_global_CW_joint_start_data
open BigOperators MME MME.TensorObj MME.ProfiledCW MME.GlobalCW MME.RegionRate MME.RegionRealization MME.RecursiveYZ MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
universe u

theorem mme_global_CW_nearby_profile_rate_bound {degree R : ℕ} {bounds : Fin R → Fin 3 → ℕ}
    {W : Type*} [Fintype W] (p : EntropyProfile degree R bounds W)
    (hpos : ∀ r c, 0 ≤ p.1 r c) (hmass : ∀ r, ∑ c, p.1 r c = 1)
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ q : EntropyProfile degree R bounds W,
      (∀ r c, 0 ≤ q.1 r c) → (∀ r, ∑ c, q.1 r c = 1) →
      (∀ r c, |q.1 r c - p.1 r c| ≤ eps) →
      (∀ i c w, |q.2 i c w - p.2 i c w| ≤ eps) →
      ∀ weights : Fin R → ℝ, (∀ r, 0 ≤ weights r) →
        p.rate weights - delta * (∑ r, weights r) ≤ q.rate weights  := by
  sorry
