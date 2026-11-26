-- Prove2me | Theorems.Thm_section5_tomography_eigenvector_recovery
-- name    : section5_tomography_eigenvector_recovery
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:59:17.261796+00:00
-- url     : https://prove2.me/theorems/df5fc1ac-3e58-5586-b383-55b9165ab652
-- title:
--   Eigenvector recovery near a rank-one projector
-- statement:
--   Let $E$ be a complex inner-product space, let $L:E\to E$ be a continuous complex linear operator, and let $w,v\in E$ be unit vectors. Let $P_w$ be the orthogonal rank-one projector onto $\mathbb Cw$. Suppose $0\le\eta<1/4$, $\lambda\ge1/2$, $\|L-P_w\|\le\eta$, and $Lv=\lambda v$ for real $\lambda$. Then
--
--   $$
--   \exists\zeta\in\mathbb C:\ |\zeta|=1\quad\text{and}\quad\|v-\zeta w\|\le4\eta.
--   $$
--
--   This turns an operator-norm approximation to a pure-state projector into a vector estimate up to global phase.
-- source:
--   Original auxiliary result supporting Section 5 of https://arxiv.org/html/2609.40331v3; this citation does not assert that the paper states the auxiliary result verbatim. Exact source: Solutions/Section5SpectralRecovery.lean, section5_tomography_eigenvector_recovery, lines 31–69.

import Mathlib
import Theorems.Thm_section5_normalize_perturbation
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace

theorem section5_tomography_eigenvector_recovery {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (L : E →L[ℂ] E) (w v : E)
    (hw : ‖w‖=1) (hv : ‖v‖=1) (η lam : ℝ) (hη : 0 ≤ η) (hη' : η < 1/4)
    (hlam : 1/2 ≤ lam) (herror : ‖L-rankOne ℂ w w‖ ≤ η)
    (heigen : L v=(lam:ℂ) • v) :
    ∃ ζ : ℂ, ‖ζ‖=1 ∧ ‖v-ζ • w‖ ≤ 4*η := by sorry
