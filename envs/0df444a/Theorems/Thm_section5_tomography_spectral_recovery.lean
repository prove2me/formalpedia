-- Prove2me | Theorems.Thm_section5_tomography_spectral_recovery
-- name    : section5_tomography_spectral_recovery
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:05:45.228812+00:00
-- url     : https://prove2.me/theorems/846825da-3879-5eaa-80f8-c0efc7fb8643
-- title:
--   Conditional spectral recovery near a rank-one projector
-- statement:
--   Let E be a complex inner-product space, L a bounded linear operator, w,v unit vectors, and 0≤η<1/4. Assume ‖L−ww*‖≤η, Lv=λv with real λ, and Re⟨x,Lx⟩≤λ for every unit x. Then $$\exists\zeta\in\mathbb C:\ |\zeta|=1,\quad\|v-\zeta w\|\le4\eta.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5SpectralRecovery.lean, lines 71–76.

import Mathlib
import Theorems.Thm_section5_tomography_eigenvector_recovery
import Theorems.Thm_section5_tomography_rayleigh_lower
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace

theorem section5_tomography_spectral_recovery {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (L : E →L[ℂ] E) (w v : E)
    (hw : ‖w‖=1) (hv : ‖v‖=1) (η lam : ℝ) (hη : 0 ≤ η) (hη' : η < 1/4)
    (herror : ‖L-rankOne ℂ w w‖ ≤ η) (heigen : L v=(lam:ℂ) • v)
    (hmax : ∀ x : E, ‖x‖=1 → (inner ℂ x (L x)).re ≤ lam) :
    ∃ ζ : ℂ, ‖ζ‖=1 ∧ ‖v-ζ • w‖ ≤ 4*η := by sorry
