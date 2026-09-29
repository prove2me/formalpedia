-- Prove2me | Theorems.Thm_mme_global_CW_counted_rate_normalization
-- name    : mme_global_CW_counted_rate_normalization
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T08:49:23.686128+00:00
-- url     : https://prove2.me/theorems/e0bdc5db-3dc6-4b9e-a362-8c4c09170597
-- title:
--   Exact identification of counted and normalized global entropy rates
-- statement:
--   Suppose a counted global stage has joint counts and joint cell-word counts equal to the corresponding real profiles multiplied by each region size. Its counting entropy rate equals the real profile rate with the region sizes as weights. The identity also handles empty regions.
-- source:
--   More Asymmetry Theorem 5.3 global stage: https://arxiv.org/html/2404.16349v2#S5. Generic finite entropy and tolerance estimates; not a completed numerical exponent certificate.

import Definitions.Def_mme_global_CW_real_entropy_profiles
import Definitions.Def_mme_global_CW_joint_start_data
open BigOperators MME MME.TensorObj MME.ProfiledCW MME.GlobalCW MME.RegionRate MME.RegionRealization MME.RecursiveYZ MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
universe u

theorem mme_global_CW_counted_rate_normalization {ell M : ℕ} (D : CountedStage ell M)
    (q : EntropyProfile D.degree D.R D.bounds (CompleteSplit.CompleteWord ell))
    (hm : ∀ r c, (D.m r c : ℝ) = (D.n r : ℝ) * q.1 r c)
    (hmu : ∀ i c w, (D.mu i c w : ℝ) = (D.n c.1 : ℝ) * q.2 i c w) :
    D.entropyRate = q.rate (fun r ↦ (D.n r : ℝ))  := by
  sorry
