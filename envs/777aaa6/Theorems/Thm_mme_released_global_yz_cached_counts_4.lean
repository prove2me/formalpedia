-- Prove2me | Theorems.Thm_mme_released_global_yz_cached_counts_4
-- name    : mme_released_global_yz_cached_counts_4
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T13:24:44.625888+00:00
-- url     : https://prove2.me/theorems/d7bff80e-eaa8-4016-a750-29b75bdf78ab
-- title:
--   Exact Y/Z word marginals in orientation 4
-- statement:
--   For orientation 4, every cached Y/Z complete-word count equals the corresponding marginal of the published exact supported joint table.
-- source:
--   Numerical global rate of the exact published More Asymmetry candidate. This closes the Y/Z branches and full global rate; whole-interface recursive continuation and the final finite witness remain separate.

import Definitions.Def_mme_released_global_yz_certificate
import Definitions.Def_mme_released_global_frame_data
import Definitions.Def_mme_global_CW_joint_start_data
open BigOperators MME MME.TensorObj MME.ProfiledCW MME.ReleasedGlobal MME.ReleasedGlobalNumeric MME.ReleasedGlobalYZ MME.MoreAsymmetryExactSeed MME.RegionRate MME.RecursiveThinSplit MME.GlobalCW MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 3000
universe u

theorem mme_released_global_yz_cached_counts_4 (i : Fin 2) (s : Fin 45) (t : Fin 81) :
    cachedCounts (4 : Fin 6) i s t =
      ((jointRows (4 : Fin 6) s).map (fun a ↦ if atom a.1 (RecursiveYZ.yzMode i) = codeWord t then a.2 else 0)).sum := by
  sorry
