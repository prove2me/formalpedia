-- Prove2me | Theorems.Thm_mme_released_global_simultaneous_uniform_window_extraction
-- name    : mme_released_global_simultaneous_uniform_window_extraction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T15:50:34.756984+00:00
-- url     : https://prove2.me/theorems/3534d29b-35c9-4186-adfe-3b6166e4c2ef
-- title:
--   All six outer extractions share one tolerance and scale threshold
-- statement:
--   One positive tolerance bound and one scale threshold support the outer source extraction for all six released owners. Every smaller positive tolerance is admissible, and the polynomial input bounds and logarithmic copy-rate estimates are retained. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_released_global_uniform_tolerance_window_extraction
import Mathlib.Data.Finset.Lattice.Fold
open BigOperators MME MME.TensorObj MME.ProfiledCW MME.ReleasedGlobal
  MME.MoreAsymmetryExactSeed MME.GlobalCW
universe u

theorem mme_released_global_simultaneous_uniform_window_extraction
    {K : Type u} [Field K] (rho : Fin 6 → ℝ)
    (hrho : ∀ owner, 0 ≤ rho owner)
    (hgap : ∀ owner, rho owner < (profile owner).rate (fun _ ↦ 1)) :
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∃ k0 : ℕ,
      ∀ eps : ℝ, 0 < eps → eps ≤ eps0 → ∀ k : ℕ, k0 ≤ k →
      ∀ owner : Fin 6,
      ∃ hk : 0 < k^2, ∃ a : Reference owner (k^2),
      ∃ S : GlobalCW.Part (4*blocks (k^2)) 3
        ((frame owner (k^2) hk a).window (windowGood owner (k^2) eps)),
        1 ≤ S.inputs ∧ S.inputs ≤ (blocks (k^2)+1)^10935 ∧
        rho owner*(blocks (k^2) : ℝ) + Real.log (S.inputs : ℝ) ≤ S.rate ∧
        Restrict (bigAdd (fun _ : Fin ⌈Real.exp S.rate⌉₊ ↦ tensor K
          ((frame owner (k^2) hk a).window (windowGood owner (k^2) eps))))
          (bigAdd (fun _ : Fin S.inputs ↦ tensor K (fun _ (_ : FineWord (4*blocks (k^2))) ↦ True))) := by sorry
