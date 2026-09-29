-- Prove2me | Theorems.Thm_mme_released_global_yz_entropy_bridge
-- name    : mme_released_global_yz_entropy_bridge
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T13:40:54.364166+00:00
-- url     : https://prove2.me/theorems/abd27d9e-e598-4fcc-9ea1-a47bbffbd7bf
-- title:
--   Identify concrete global Y/Z rates with their exact signed-log certificates
-- statement:
--   For each of six exact published profiles and each Y/Z branch, the signed-log certificate equals its actual coarse entropy plus word entropy minus compatibility entropy.
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

theorem mme_released_global_yz_entropy_bridge (o : Fin 6) (i : Fin 2) :
    evaluate ((entries o i).map Prod.fst) =
      (profile o).coarse (yzMode i) 0 + (profile o).words (yzMode i) 0 - (profile o).compat i 0 := by
  sorry
