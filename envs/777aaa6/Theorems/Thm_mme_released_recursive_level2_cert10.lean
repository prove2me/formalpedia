-- Prove2me | Theorems.Thm_mme_released_recursive_level2_cert10
-- name    : mme_released_recursive_level2_cert10
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-23T01:01:41.054419+00:00
-- url     : https://prove2.me/theorems/aa404124-c9c5-42a6-9b96-38622c24f2ec
-- title:
--   Certified entropy floors for level-two regions 920 to 1011
-- statement:
--   The certified entropy floors of level-two regions 920 to 1011.
--
--   For each region the published certificate data names a reference value for each of the three grades
--   of its parametric mode, and a rational floor. This says that floor really is a lower bound for the
--   Gibbs bound built from those references, so, by the published region bound, it is a lower bound for
--   the region's entropy.
-- source:
--   Duan-Wu-Zhou fourth-power recursive construction (https://arxiv.org/html/2210.10173v5, section 7) combined with the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6). Exact finite or asymptotic-rate statement as written; no exponent claim.

import Mathlib
import Definitions.Def_mme_released_recursive_level2_cert_data
import Definitions.Def_mme_released_recursive_level2_uniform_data
import Definitions.Def_mme_released_recursive_level2_floor_data
import Definitions.Def_mme_released_recursive_level2_split_data
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_certified_entropy_rational_data
import Theorems.Thm_mme_released_recursive_level2_floor_cases
import Theorems.Thm_mme_released_recursive_level2_marginals
open BigOperators MME MME.RecursiveYZ MME.RecStage MME.Cert MME.L2Cert
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem mme_released_recursive_level2_cert10 : ∀ j : Fin 92,
    ((certNum ⟨920 + j.val, by omega⟩ : Int) : ℚ)/10^30 ≤
      regFloor (certMode ⟨920 + j.val, by omega⟩) ⟨920 + j.val, by omega⟩
        (certE ⟨920 + j.val, by omega⟩) := by sorry
