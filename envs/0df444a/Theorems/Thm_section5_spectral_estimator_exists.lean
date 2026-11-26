-- Prove2me | Theorems.Thm_section5_spectral_estimator_exists
-- name    : section5_spectral_estimator_exists
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:10:22.546677+00:00
-- url     : https://prove2.me/theorems/85fdbfdc-22b1-5d77-a972-e27a11c2029f
-- title:
--   Existence of a conditional spectral estimator
-- statement:
--   Let E be a nontrivial finite-dimensional complex inner-product space and L self-adjoint. There exists a unit vector v such that for every unit w and 0≤η<1/4, $$\|L-ww^*\|\le\eta\implies\exists\zeta\in\mathbb C:\ |\zeta|=1,\quad\|v-\zeta w\|\le4\eta.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5SpectralRecovery.lean, lines 81–85.

import Mathlib
import Theorems.Thm_section5_tomography_spectral_recovery
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace

theorem section5_spectral_estimator_exists {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [Nontrivial E]
    (L : E →L[ℂ] E) (hL : IsSelfAdjoint L) :
    ∃ v : E, ‖v‖=1 ∧ ∀ w : E, ‖w‖=1 → ∀ η : ℝ, 0 ≤ η → η < 1/4 →
      ‖L-rankOne ℂ w w‖ ≤ η → ∃ ζ : ℂ, ‖ζ‖=1 ∧ ‖v-ζ • w‖ ≤ 4*η := by sorry
