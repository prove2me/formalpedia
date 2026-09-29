-- Prove2me | Theorems.Thm_mme_released_global_yz_data_valid
-- name    : mme_released_global_yz_data_valid
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T13:40:35.391989+00:00
-- url     : https://prove2.me/theorems/b5224dcb-b641-42ed-a8b0-90fe92ef92ac
-- title:
--   Exact word marginals and rational Y/Z entropy certificates for six orientations
-- statement:
--   Validate all cached word counts against the published sparse supported joint table, identify the 3822 signed logarithm terms with the exact rational mass-entropy expressions, and prove both Y/Z rational interval bounds exceed the six existing rate floors.
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

theorem mme_released_global_yz_data_valid :
    (∀ o i s t, cachedCounts o i s t =
      ((jointRows o s).map (fun a ↦ if atom a.1 (RecursiveYZ.yzMode i) = codeWord t then a.2 else 0)).sum) ∧
    (∀ o i, (entries o i).map Prod.fst = prune (rawTerms o i)) ∧
    (∀ o i, rateFloor o ≤ totalBound o i) := by
  sorry
