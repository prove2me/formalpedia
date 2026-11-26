-- Prove2me | Theorems.Thm_section5_max_column_recovery
-- name    : section5_max_column_recovery
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:57:07.951877+00:00
-- url     : https://prove2.me/theorems/97b3afcc-11a5-5dcc-b443-24bcb2f85be9
-- title:
--   Recovery from a maximum norm column
-- statement:
--   Let $n\ge1$, let $A$ act on $\mathbb C^n$, let $v$ be unit, and let $e_j$ be a standard basis vector whose image under $A$ has maximum column norm. Suppose $\alpha>0$, $\rho\ge0$, $4n\rho\le\alpha$, and $\|A-\alpha vv^*\|\le\rho$. Then
--
--   $$Ae_j
--   e0,\qquad\exists\zeta\in\mathbb C:\ |\zeta|=1,\quad\left\|\frac{Ae_j}{\|Ae_j\|}-\zeta v\right\|\le\frac{4n\rho}{\alpha}.$$
--
--   This supplies a column-based estimator under an explicit rank-one approximation hypothesis.
-- source:
--   Original auxiliary result for Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5 (formalization support, not an assertion that the paper states this auxiliary lemma verbatim). Exact formalization: Solutions/Section5PowerColumnRecovery.lean, lines 38–101.

import Definitions.Def_Section5Verified_Section5PowerColumnRecovery
import Mathlib
import Theorems.Thm_section5_column_norm_bound
import Theorems.Thm_section5_normalize_perturbation
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace

theorem section5_max_column_recovery {n : ℕ} (hn : 1 ≤ n)
    (A : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (j : Fin n) (hmax : ∀ i, ‖A (section5_coordinate_ket i)‖ ≤ ‖A (section5_coordinate_ket j)‖)
    (v : EuclideanSpace ℂ (Fin n)) (hv : ‖v‖=1)
    (α ρ : ℝ) (hα : 0 < α) (hρ : 0 ≤ ρ) (hsmall : 4*n*ρ ≤ α)
    (herror : ‖A-(α:ℂ) • rankOne ℂ v v‖ ≤ ρ) :
    A (section5_coordinate_ket j) ≠ 0 ∧
      ∃ ζ : ℂ, ‖ζ‖=1 ∧
        ‖NormedSpace.normalize (A (section5_coordinate_ket j))-ζ • v‖ ≤ 4*n*ρ/α := by sorry
