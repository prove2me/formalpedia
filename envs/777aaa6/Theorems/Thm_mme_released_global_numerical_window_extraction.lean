-- Prove2me | Theorems.Thm_mme_released_global_numerical_window_extraction
-- name    : mme_released_global_numerical_window_extraction
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T13:40:54.151501+00:00
-- url     : https://prove2.me/theorems/3c296d8f-558e-4e4a-8d60-d38e1fc1a016
-- title:
--   Numerically certified concrete global window extraction
-- statement:
--   For any nonnegative rho strictly below the published floor in an orientation and any positive tolerance cap, the exact supported global candidate admits the cofinal square-scale window extraction, polynomial input bound and actual tensor restriction.
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

theorem mme_released_global_numerical_window_extraction {K : Type u} [Field K] (owner : Fin 6) (rho eta : ℝ)
    (hrho : 0 ≤ rho) (hgap : rho < (ReleasedGlobalNumeric.rateFloor owner : ℝ)) (heta : 0 < eta) :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ eta ∧ ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∃ hk : 0 < k^2, ∃ a : Reference owner (k^2),
      ∃ S : GlobalCW.Part (4*blocks (k^2)) 3
        ((frame owner (k^2) hk a).window (windowGood owner (k^2) eps)),
        1 ≤ S.inputs ∧ S.inputs ≤ (blocks (k^2)+1)^10935 ∧
        rho*(blocks (k^2) : ℝ) + Real.log (S.inputs : ℝ) ≤ S.rate ∧
        Restrict (bigAdd (fun _ : Fin ⌈Real.exp S.rate⌉₊ ↦ tensor K
          ((frame owner (k^2) hk a).window (windowGood owner (k^2) eps))))
          (bigAdd (fun _ : Fin S.inputs ↦ tensor K (fun _ (_ : FineWord (4*blocks (k^2))) ↦ True))) := by
  sorry
