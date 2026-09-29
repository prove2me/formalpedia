-- Prove2me | Theorems.Thm_mme_released_global_uniform_tolerance_window_extraction
-- name    : mme_released_global_uniform_tolerance_window_extraction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T15:26:44.878303+00:00
-- url     : https://prove2.me/theorems/ad2e56fd-b25e-4a14-adeb-c23937ca0171
-- title:
--   One outer scale threshold works for every sufficiently small tolerance
-- statement:
--   For each released owner and every nonnegative rate below its global profile rate, one positive tolerance bound and one scale threshold support the actual outer source extraction for every smaller positive tolerance. The polynomial input bound and logarithmic copy-rate estimate are retained. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Definitions.Def_mme_released_global_frame_data
import Definitions.Def_mme_global_CW_joint_start_data
import Theorems.Thm_mme_released_global_joint_counts_valid
import Theorems.Thm_mme_released_global_supported_frame
import Theorems.Thm_mme_released_global_uniform_window_bounds
import Theorems.Thm_mme_global_CW_histogram_window_cofinal_extraction
open BigOperators MME MME.TensorObj MME.ProfiledCW MME.ReleasedGlobal MME.MoreAsymmetryExactSeed MME.GlobalCW MME.RegionRate MME.RecursiveYZ
open scoped Classical
universe u

theorem mme_released_global_uniform_tolerance_window_extraction {K : Type u} [Field K] (owner : Fin 6) (rho : ℝ)
    (hrho : 0 ≤ rho) (hgap : rho < (profile owner).rate (fun _ ↦ 1)) :
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∃ k0 : ℕ,
      ∀ eps : ℝ, 0 < eps → eps ≤ eps0 → ∀ k : ℕ, k0 ≤ k →
      ∃ hk : 0 < k^2, ∃ a : Reference owner (k^2),
      ∃ S : GlobalCW.Part (4*blocks (k^2)) 3
        ((frame owner (k^2) hk a).window (windowGood owner (k^2) eps)),
        1 ≤ S.inputs ∧ S.inputs ≤ (blocks (k^2)+1)^10935 ∧
        rho*(blocks (k^2) : ℝ) + Real.log (S.inputs : ℝ) ≤ S.rate ∧
        Restrict (bigAdd (fun _ : Fin ⌈Real.exp S.rate⌉₊ ↦ tensor K
          ((frame owner (k^2) hk a).window (windowGood owner (k^2) eps))))
          (bigAdd (fun _ : Fin S.inputs ↦ tensor K (fun _ (_ : FineWord (4*blocks (k^2))) ↦ True))) := by sorry
