-- Prove2me | Theorems.Thm_mme_released_global_profile_count_identities
-- name    : mme_released_global_profile_count_identities
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T11:21:44.39599+00:00
-- url     : https://prove2.me/theorems/1fc70a5c-7e5e-44cf-8cf9-1dcc26f434e4
-- title:
--   Exact global candidate has consistent supported joint and marginal counts
-- statement:
--   For every owner, the global coarse counts sum to 10^60. The joint counts have precisely those coarse masses; all positive entries satisfy the coarse grades and pointwise CW support; every mode marginal has the same coarse mass.
-- source:
--   Concrete global profile obligations for More Asymmetry Theorem 5.3, https://arxiv.org/html/2404.16349v2#S5 . This is an explicit rational candidate reconstructed from the released primitive seed; the numerical rate inequalities and whole-interface continuation remain separate obligations.

import Definitions.Def_mme_released_global_frame_data
import Definitions.Def_mme_global_CW_joint_start_data
open BigOperators MME MME.TensorObj MME.ProfiledCW MME.ReleasedGlobal MME.MoreAsymmetryExactSeed MME.GlobalCW MME.RegionRate MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 3000
universe u

theorem mme_released_global_profile_count_identities (owner : Fin 6) :
    (∑ c : Shape, coarseCounts owner c) = denominator^5 ∧
    (∀ c : Shape, ∑ v : JointWord, jointCounts owner c v = coarseCounts owner c) ∧
    (∀ c v, 0 < jointCounts owner c v →
      (∀ i, CWCells.grade (v i) = (c.val i).val) ∧
      ∀ r, (v 0 r).val + (v 1 r).val + (v 2 r).val = 2) ∧
    (∀ i c, ∑ w : Word, wordCounts owner i c w = coarseCounts owner c) := by
  sorry
