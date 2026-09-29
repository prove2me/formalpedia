-- Prove2me | Theorems.Thm_mme_released_global_conditional_histogram_center
-- name    : mme_released_global_conditional_histogram_center
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T02:27:19.634185+00:00
-- url     : https://prove2.me/theorems/a3b2b55f-4164-48ab-a99b-ab9d4c12b628
-- title:
--   Conditional global histogram centers equal released row marginals
-- statement:
--   For any released coarse cell with positive coarse weight and positive replication, rescaling its global profile center by total blocks divided by cell size gives exactly the marginal of its released joint-row list divided by denominator to the fourth power. The proof first identifies the finite joint-count marginal and then cancels scale factors.
-- source:
--   Exact cell fiber counting, simultaneous tensor extraction and histogram normalization.

import Definitions.Def_mme_released_global_frame_data
open BigOperators MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
set_option autoImplicit false
universe u
universe v w

theorem mme_released_global_conditional_histogram_center
    (owner : Fin 6) (c : Shape) (hc : 0 < alpha owner (shapeEquiv.symm c))
    (k : ℕ) (hk : 0 < k) (i : Fin 3) (w : Word) :
    ((blocks k : ℝ) / ((k * coarseCounts owner c : ℕ) : ℝ)) *
        (profile owner).2 i ⟨0,c⟩ w =
      ((((jointRows owner (shapeEquiv.symm c)).map
        (fun a ↦ if atom a.1 i = w then a.2 else 0)).sum : ℕ) : ℝ) /
          (denominator : ℝ)^4 := by sorry
