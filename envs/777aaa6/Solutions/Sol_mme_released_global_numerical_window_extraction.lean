-- Prove2me | solution 1 for mme_released_global_numerical_window_extraction
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T14:17:25.140156+00:00
-- url     : https://prove2.me/submissions/d5ac1279-6fed-44aa-9cee-b2b837e9277c

import Definitions.Def_mme_released_global_yz_certificate
import Definitions.Def_mme_released_global_frame_data
import Definitions.Def_mme_global_CW_joint_start_data
import Theorems.Thm_mme_released_global_rate_floor
import Theorems.Thm_mme_released_global_window_extraction
open BigOperators MME MME.TensorObj MME.ProfiledCW MME.ReleasedGlobal MME.MoreAsymmetryExactSeed MME.GlobalCW MME.RegionRate MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 3000
universe u

theorem solution {K : Type u} [Field K] (owner : Fin 6) (rho eta : ℝ)
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
  exact mme_released_global_window_extraction owner rho eta hrho
    (hgap.trans_le (mme_released_global_rate_floor owner)) heta
