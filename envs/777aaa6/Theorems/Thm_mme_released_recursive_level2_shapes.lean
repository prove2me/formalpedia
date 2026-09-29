-- Prove2me | Theorems.Thm_mme_released_recursive_level2_shapes
-- name    : mme_released_recursive_level2_shapes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-22T22:02:53.933696+00:00
-- url     : https://prove2.me/theorems/1a74fd3d-dc7d-4605-80a2-8764ba5233f4
-- title:
--   The level-two table has only three parent shapes
-- statement:
--   Two facts about the published level-two table of the released recursive construction.
--
--   Every one of its 1104 regions has one of only three parent shapes: the leading pair of grades is
--   (1,1), (1,2) or (2,1), so the parent triple is (1,1,2), (1,2,1) or (2,1,1). And in every region the
--   free weight parameter is at most half the scale, so the middle weight of the split is a genuine
--   natural number.
--
--   Both are finite checks over the table, verified by exact evaluation.
-- source:
--   Duan-Wu-Zhou fourth-power recursive construction (https://arxiv.org/html/2210.10173v5, section 7) combined with the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6). Exact finite or asymptotic-rate statement as written; no exponent claim.

import Mathlib
import Definitions.Def_mme_released_recursive_level2_split_data
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
open BigOperators MME MME.RecursiveYZ MME.RecStage MME.L2Cert
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem mme_released_recursive_level2_shapes :
    (∀ r : Fin 1104,
      ((l2At r).1.1 = 1 ∧ (l2At r).1.2.1 = 1) ∨ ((l2At r).1.1 = 1 ∧ (l2At r).1.2.1 = 2) ∨
        ((l2At r).1.1 = 2 ∧ (l2At r).1.2.1 = 1)) ∧
    ∀ r : Fin 1104, 2 * (l2At r).2.2 ≤ D := by sorry
