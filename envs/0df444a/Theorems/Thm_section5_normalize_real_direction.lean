-- Prove2me | Theorems.Thm_section5_normalize_real_direction
-- name    : section5_normalize_real_direction
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:57:11.479261+00:00
-- url     : https://prove2.me/theorems/6ea07f47-0601-5858-bbc6-d9b915f01fba
-- title:
--   Stable recovery of a real direction after normalization
-- statement:
--   Let $V$ be a real normed vector space, let $r,w\in V$, and let $c,\delta\in\mathbb R$. Suppose $\|w\|=1$, $|c|>1/2$, $0\le\delta<1/2$, and $\|r-cw\|\le\delta$. Then
--
--   $$
--   r\ne0,\qquad\left\|\frac{r}{\|r\|}-\operatorname{sgn}(c)w\right\|\le4\delta.
--   $$
--
--   This controls normalized direction error when a vector approximates a sufficiently large real multiple of a unit vector.
-- source:
--   Original auxiliary result supporting Section 5 of https://arxiv.org/html/2609.40331v3; not asserted to be a separately numbered result of the paper. Exact local source: Solutions/Section5Normalize.lean, section5_normalize_real_direction, lines 23–43.

import Mathlib
import Theorems.Thm_section5_normalize_perturbation
set_option autoImplicit false

theorem section5_normalize_real_direction {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (r w : V) (c δ : ℝ) (hw : ‖w‖ = 1)
    (hc : 1/2 < |c|) (hδ : 0 ≤ δ) (hδ' : δ < 1/2)
    (hclose : ‖r - c • w‖ ≤ δ) :
    r ≠ 0 ∧ ‖‖r‖⁻¹ • r - (SignType.sign c : ℝ) • w‖ ≤ 4 * δ := by sorry
