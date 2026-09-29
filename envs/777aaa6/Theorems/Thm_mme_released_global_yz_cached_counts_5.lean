-- Prove2me | Theorems.Thm_mme_released_global_yz_cached_counts_5
-- name    : mme_released_global_yz_cached_counts_5
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T13:29:10.281333+00:00
-- url     : https://prove2.me/theorems/7878edd1-cde6-4d45-a3c6-f88fe7211912
-- title:
--   Exact Y/Z word marginals in orientation 5
-- statement:
--   For orientation 5, every cached Y/Z complete-word count equals the corresponding marginal of the published exact supported joint table.
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

theorem mme_released_global_yz_cached_counts_5 (i : Fin 2) (s : Fin 45) (t : Fin 81) :
    cachedCounts (5 : Fin 6) i s t =
      ((jointRows (5 : Fin 6) s).map (fun a ↦ if atom a.1 (RecursiveYZ.yzMode i) = codeWord t then a.2 else 0)).sum := by
  sorry
