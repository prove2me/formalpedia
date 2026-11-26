-- Prove2me | Theorems.Thm_section5_power_column_estimator
-- name    : section5_power_column_estimator
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:12:25.485952+00:00
-- url     : https://prove2.me/theorems/d3e207f5-4b58-4638-a191-ea3a36676dec
-- title:
--   Conditional recovery from a maximum powered column
-- statement:
--   Let n≥1, L self-adjoint on C^n, 0<ε<1, 2^(k+1)≥400n/ε, and j maximize the column norms of L^(k+1). For any unit w satisfying ‖L−ww*‖≤ε/1000, $$L^{k+1}e_j\ne0,\qquad\exists|\zeta|=1:\ \left\|\frac{L^{k+1}e_j}{\|L^{k+1}e_j\|}-\zeta w\right\|\le\varepsilon/24.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5PowerReconstruction.lean, lines 12–22.

import Definitions.Def_Section5Verified_Section5PowerColumnRecovery
import Mathlib
import Theorems.Thm_section5_max_column_recovery
import Theorems.Thm_section5_tomography_eigenvector_recovery
import Theorems.Thm_section5_tomography_power_error
import Theorems.Thm_section5_tomography_rayleigh_lower
import Theorems.Thm_section5_top_eigenpair_exists
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace

theorem section5_power_column_estimator {n : ℕ} (hn : 1 ≤ n)
    (L : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (hL : IsSelfAdjoint L)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) (k : ℕ)
    (hprec : 400*(n:ℝ)/ε ≤ (2:ℝ)^(k+1))
    (j : Fin n) (hmax : ∀ i, ‖(L^(k+1)) (section5_coordinate_ket i)‖ ≤
      ‖(L^(k+1)) (section5_coordinate_ket j)‖)
    (w : EuclideanSpace ℂ (Fin n)) (hw : ‖w‖=1)
    (herror : ‖L-rankOne ℂ w w‖ ≤ ε/1000) :
    (L^(k+1)) (section5_coordinate_ket j) ≠ 0 ∧
      ∃ ζ : ℂ, ‖ζ‖=1 ∧
        ‖NormedSpace.normalize ((L^(k+1)) (section5_coordinate_ket j))-ζ • w‖ ≤ ε/24 := by sorry
