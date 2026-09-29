-- Prove2me | Theorems.Thm_mme_released_global_window_extraction
-- name    : mme_released_global_window_extraction
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T11:22:05.539103+00:00
-- url     : https://prove2.me/theorems/dbe54579-728f-4bdb-b03b-9867b3afb055
-- title:
--   Actual extraction for the concrete six-orientation global candidate
-- statement:
--   For every orientation, nonnegative rho below its exact central entropy rate, and positive upper tolerance eta, choose a fixed positive eps at most eta. At all sufficiently large square scales, construct an actual GlobalCW.Part and tensor restriction for the concrete profile window. Net logarithmic copies are at least rho times the number of original blocks, after paying for all exact input types and finite extraction losses.
-- source:
--   Concrete global profile obligations for More Asymmetry Theorem 5.3, https://arxiv.org/html/2404.16349v2#S5 . This is an explicit rational candidate reconstructed from the released primitive seed; the numerical rate inequalities and whole-interface continuation remain separate obligations.

import Definitions.Def_mme_released_global_frame_data
import Definitions.Def_mme_global_CW_joint_start_data
open BigOperators MME MME.TensorObj MME.ProfiledCW MME.ReleasedGlobal MME.MoreAsymmetryExactSeed MME.GlobalCW MME.RegionRate MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 3000
universe u

theorem mme_released_global_window_extraction {K : Type u} [Field K] (owner : Fin 6) (rho eta : ℝ)
    (hrho : 0 ≤ rho) (hgap : rho < (profile owner).rate (fun _ ↦ 1)) (heta : 0 < eta) :
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
