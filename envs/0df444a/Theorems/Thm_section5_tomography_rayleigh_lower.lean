-- Prove2me | Theorems.Thm_section5_tomography_rayleigh_lower
-- name    : section5_tomography_rayleigh_lower
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:59:09.212872+00:00
-- url     : https://prove2.me/theorems/b7ce2ba6-25af-4754-a1a5-04fcfc59da5a
-- title:
--   Rayleigh upper bounds near a pure-state projector are large
-- statement:
--   Let $E$ be a complex inner-product space, $L:E\to E$ a continuous complex linear operator, and $w\in E$ a unit vector. Let $P_w$ be the orthogonal projector onto $\mathbb Cw$. Suppose $\|L-P_w\|\le\eta$ and every unit vector $x\in E$ satisfies $\operatorname{Re}\langle x,Lx\rangle\le\lambda$, for real $\eta,\lambda$. Then
--
--   $$
--   1-\eta\le\lambda.
--   $$
--
--   This lower-bounds any common upper bound on the real Rayleigh quotients of an operator close to a pure-state projector.
-- source:
--   Original auxiliary result supporting Section 5 of https://arxiv.org/html/2609.40331v3; this citation does not assert that the paper states the auxiliary result verbatim. Exact source: Solutions/Section5SpectralRecovery.lean, section5_tomography_rayleigh_lower, lines 11–29.

import Mathlib
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace

theorem section5_tomography_rayleigh_lower {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (L : E →L[ℂ] E) (w : E) (hw : ‖w‖=1)
    (η lam : ℝ) (herror : ‖L-rankOne ℂ w w‖ ≤ η)
    (hmax : ∀ x : E, ‖x‖=1 → (inner ℂ x (L x)).re ≤ lam) :
    1-η ≤ lam := by sorry
