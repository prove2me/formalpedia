-- Prove2me | Theorems.Thm_section5_tomography_deflated_norm
-- name    : section5_tomography_deflated_norm
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:05:25.966544+00:00
-- url     : https://prove2.me/theorems/753d97ff-d8df-57ee-9cc8-61a11341ca5c
-- title:
--   Conditional residual norm after spectral deflation
-- statement:
--   Let L be bounded on a complex inner-product space, w,v unit vectors, 0≤η<1/4, and λ real with λ≥1/2 and λ≥1−η. If ‖L−ww*‖≤η and Lv=λv, then $$\|L-\lambda vv^*\|\le10\eta.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5SpectralDeflation.lean, lines 30–35.

import Mathlib
import Theorems.Thm_section5_tomography_eigenvector_recovery
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace

theorem section5_tomography_deflated_norm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (L : E →L[ℂ] E) (w v : E)
    (hw : ‖w‖=1) (hv : ‖v‖=1) (η lam : ℝ) (hη : 0 ≤ η) (hη' : η < 1/4)
    (hlam : 1/2 ≤ lam) (hlow : 1-η ≤ lam)
    (herror : ‖L-rankOne ℂ w w‖ ≤ η) (heigen : L v=(lam:ℂ) • v) :
    ‖L-(lam:ℂ) • rankOne ℂ v v‖ ≤ 10*η := by sorry
