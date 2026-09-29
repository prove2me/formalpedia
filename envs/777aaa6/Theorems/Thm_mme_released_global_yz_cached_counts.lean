-- Prove2me | Theorems.Thm_mme_released_global_yz_cached_counts
-- name    : mme_released_global_yz_cached_counts
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T13:40:10.075849+00:00
-- url     : https://prove2.me/theorems/45d4c7a2-9b70-4584-8fa3-977118523133
-- title:
--   Grouped exact word counts for the six global profiles
-- statement:
--   Every cached Y/Z word count equals the corresponding marginal of the published exact sparse joint table.
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

theorem mme_released_global_yz_cached_counts (o : Fin 6) (i : Fin 2) (s : Fin 45) (t : Fin 81) :
    cachedCounts o i s t =
      ((jointRows o s).map (fun a ↦ if atom a.1 (RecursiveYZ.yzMode i) = codeWord t then a.2 else 0)).sum := by
  sorry
