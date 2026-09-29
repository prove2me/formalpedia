-- Prove2me | Theorems.Thm_mme_released_global_sparse_marginals
-- name    : mme_released_global_sparse_marginals
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T11:30:19.603583+00:00
-- url     : https://prove2.me/theorems/0fefdea4-b793-45f5-8e3e-cffc2546256d
-- title:
--   Compute concrete global marginals directly from the sparse supported table
-- statement:
--   Every marginal word count equals its coarse alpha weight times the sparse joint table summed only over atoms with the requested mode word. This exact Lean identity avoids enumerating the full 81 cubed joint-word alphabet when certifying the numerical profile.
-- source:
--   Concrete global profile obligations for More Asymmetry Theorem 5.3, https://arxiv.org/html/2404.16349v2#S5 . This is an explicit rational candidate reconstructed from the released primitive seed; the numerical rate inequalities and whole-interface continuation remain separate obligations.

import Definitions.Def_mme_released_global_profile_data
open BigOperators MME MME.ReleasedGlobal
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false

theorem mme_released_global_sparse_marginals (owner : Fin 6) (c : Shape) (i : Fin 3) (w : Word) :
    wordCounts owner i c w = alpha owner (shapeEquiv.symm c) *
      ((jointRows owner (shapeEquiv.symm c)).map
        (fun a ↦ if atom a.1 i = w then a.2 else 0)).sum := by
  sorry
