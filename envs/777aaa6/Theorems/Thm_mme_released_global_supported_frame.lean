-- Prove2me | Theorems.Thm_mme_released_global_supported_frame
-- name    : mme_released_global_supported_frame
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T11:20:54.838341+00:00
-- url     : https://prove2.me/theorems/f5bab9eb-8043-4e2e-9f4f-24ad7ccb559a
-- title:
--   Concrete global candidate yields a supported nonempty window at every positive scale
-- statement:
--   For each of the six orientations and every positive integer k, construct an actual global coarse frame of 10^60 k blocks with admissible exact complete-word counts and a supported word triple in every nonnegative tolerance window around the explicit profile.
-- source:
--   Concrete global profile obligations for More Asymmetry Theorem 5.3, https://arxiv.org/html/2404.16349v2#S5 . This is an explicit rational candidate reconstructed from the released primitive seed; the numerical rate inequalities and whole-interface continuation remain separate obligations.

import Definitions.Def_mme_released_global_frame_data
import Definitions.Def_mme_global_CW_joint_start_data
open BigOperators MME MME.TensorObj MME.ProfiledCW MME.ReleasedGlobal MME.MoreAsymmetryExactSeed MME.GlobalCW MME.RegionRate MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 3000
universe u

theorem mme_released_global_supported_frame (owner : Fin 6) (k : ℕ) (hk : 0 < k) :
    ∃ a : Reference owner k,
      (frame owner k hk a).Admissible (scaledWords owner k) ∧
      ∀ eps : ℝ, 0 ≤ eps →
      ∃ x : Fin 3 → FineWord (4*blocks k), supported x ∧
        ∀ i, (frame owner k hk a).window (windowGood owner k eps) i (x i) := by
  sorry
