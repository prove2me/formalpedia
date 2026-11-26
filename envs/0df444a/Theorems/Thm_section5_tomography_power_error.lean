-- Prove2me | Theorems.Thm_section5_tomography_power_error
-- name    : section5_tomography_power_error
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:09:54.691805+00:00
-- url     : https://prove2.me/theorems/3a9c7dde-55ae-52e2-ad6a-5723b082903e
-- title:
--   Conditional error of a powered near-rank-one operator
-- statement:
--   Let L be self-adjoint on a nontrivial complex Hilbert space, w,v unit, 0≤η<1/4, and λ≥max{1/2,1−η} real. Assume ‖L−ww*‖≤η and Lv=λv. For every natural k, $$\|L^{k+1}-\lambda^{k+1}vv^*\|\le(10\eta)^{k+1}.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5SpectralDeflation.lean, lines 134–140.

import Mathlib
import Theorems.Thm_section5_tomography_deflated_norm
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace

theorem section5_tomography_power_error {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
    (L : E →L[ℂ] E) (hL : IsSelfAdjoint L) (w v : E)
    (hw : ‖w‖=1) (hv : ‖v‖=1) (η lam : ℝ) (hη : 0 ≤ η) (hη' : η < 1/4)
    (hlam : 1/2 ≤ lam) (hlow : 1-η ≤ lam)
    (herror : ‖L-rankOne ℂ w w‖ ≤ η) (heigen : L v=(lam:ℂ) • v) (k : ℕ) :
    ‖L^(k+1)-((lam^(k+1):ℝ):ℂ) • rankOne ℂ v v‖ ≤ (10*η)^(k+1) := by sorry
