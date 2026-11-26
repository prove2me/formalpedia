-- Prove2me | Theorems.Thm_section5_tomography_real_reconstruction
-- name    : section5_tomography_real_reconstruction
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:12:41.095826+00:00
-- url     : https://prove2.me/theorems/478646da-d80f-42d1-ac0e-6c9d27c40f2b
-- title:
--   Conditional real-direction recovery from a spectral estimate
-- statement:
--   Let n≥1 and L be self-adjoint on complex n-dimensional Euclidean space. There is a unit v such that, for every real unit w and 0<ε<1 with ‖L−ww*‖≤ε/96, selecting r as the larger-norm real or imaginary part of v gives $$r\ne0,\qquad\min\{\|r/\|r\|-w\|,\|r/\|r\|+w\|\}\le\varepsilon/6.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5TomographyReconstruction.lean, lines 19–27.

import Definitions.Def_Section5Verified_Section5PhaseRecovery
import Mathlib
import Theorems.Thm_section5_real_direction_recovery
import Theorems.Thm_section5_spectral_estimator_exists
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace

theorem section5_tomography_real_reconstruction (n : ℕ) (hn : 1 ≤ n)
    (L : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (hL : IsSelfAdjoint L) :
    ∃ v : EuclideanSpace ℂ (Fin n), ‖v‖=1 ∧
      ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖=1 →
      ∀ ε : ℝ, 0 < ε → ε < 1 →
      ‖L-rankOne ℂ (section5_complexify w) (section5_complexify w)‖ ≤ ε/96 →
        let r := if ‖section5_imag_part v‖ ≤ ‖section5_real_part v‖ then
          section5_real_part v else section5_imag_part v
        r ≠ 0 ∧ (‖NormedSpace.normalize r-w‖ ≤ ε/6 ∨ ‖NormedSpace.normalize r+w‖ ≤ ε/6) := by sorry
