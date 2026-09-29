-- Prove2me | solution 1 for mme_released_recursive_level2_shapes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-22T22:03:04.726051+00:00
-- url     : https://prove2.me/submissions/8ee005c9-55ed-442c-82e6-3cc2389cfbe7

import Mathlib
import Definitions.Def_mme_released_recursive_level2_split_data
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
open BigOperators MME MME.RecursiveYZ MME.RecStage MME.L2Cert
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem solution :
    (∀ r : Fin 1104,
      ((l2At r).1.1 = 1 ∧ (l2At r).1.2.1 = 1) ∨ ((l2At r).1.1 = 1 ∧ (l2At r).1.2.1 = 2) ∨
        ((l2At r).1.1 = 2 ∧ (l2At r).1.2.1 = 1)) ∧
    ∀ r : Fin 1104, 2 * (l2At r).2.2 ≤ D := by
  refine ⟨?_, ?_⟩
  · decide +kernel
  · decide +kernel
