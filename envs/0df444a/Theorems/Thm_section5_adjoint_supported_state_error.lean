-- Prove2me | Theorems.Thm_section5_adjoint_supported_state_error
-- name    : section5_adjoint_supported_state_error
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:36:27.730568+00:00
-- url     : https://prove2.me/theorems/371ac3e1-f119-551f-a4ab-1319bd61bcde
-- title:
--   Adjoint error for a supported state
-- statement:
--   Let $E,H$ be complex Hilbert spaces and let $T,A,S:E\to H$ be bounded linear maps. Let $\psi,\phi\in H$ and $\delta,\varepsilon\in\mathbb R$ satisfy $\|T\|\le1$, $\|S-A\|\le\delta$, $\|\psi\|\le1$, $A^*\psi=T^*\psi$, and $\|\psi-\phi\|\le\varepsilon$. Then
--
--   $$\|S^*\psi-T^*\phi\|\le\delta+\varepsilon.$$
--
--   This combines synthesis-map error with state error when the restricted and full adjoints agree on the sampled state.
-- source:
--   Original functional-analytic auxiliary result for Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3, Section 5.1. Formalization: Solutions/Section5L2Synthesis.lean, lines 111–136.

import Mathlib
set_option autoImplicit false
open MeasureTheory

theorem section5_adjoint_supported_state_error
    {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T A S : E →L[ℂ] H) (ψ φ : H) (δ ε : ℝ)
    (hT : ‖T‖ ≤ 1) (hAS : ‖S-A‖ ≤ δ) (hψ : ‖ψ‖ ≤ 1)
    (hsupport : ContinuousLinearMap.adjoint A ψ=ContinuousLinearMap.adjoint T ψ)
    (hstates : ‖ψ-φ‖ ≤ ε) :
    ‖ContinuousLinearMap.adjoint S ψ-ContinuousLinearMap.adjoint T φ‖ ≤ δ+ε := by sorry
