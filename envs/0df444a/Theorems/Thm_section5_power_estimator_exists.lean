-- Prove2me | Theorems.Thm_section5_power_estimator_exists
-- name    : section5_power_estimator_exists
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:16:27.834626+00:00
-- url     : https://prove2.me/theorems/94109fa0-564a-4f47-9995-d2daf1d1a744
-- title:
--   Existence of a conditional powered-column estimator
-- statement:
--   Let n≥1, L self-adjoint on C^n, 0<ε<1 and 2^(k+1)≥400n/ε. There exists a column index j, chosen independently of w, such that for every unit w with ‖L−ww*‖≤ε/1000, $$L^{k+1}e_j\ne0,\qquad\exists|\zeta|=1:\ \left\|\frac{L^{k+1}e_j}{\|L^{k+1}e_j\|}-\zeta w\right\|\le\varepsilon/24.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5PowerReconstruction.lean, lines 69–77.

import Definitions.Def_Section5Verified_Section5PowerColumnRecovery
import Mathlib
import Theorems.Thm_section5_power_column_estimator
set_option autoImplicit false
open ContinuousLinearMap InnerProductSpace

theorem section5_power_estimator_exists {n : ℕ} (hn : 1 ≤ n)
    (L : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) (hL : IsSelfAdjoint L)
    (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1) (k : ℕ)
    (hprec : 400*(n:ℝ)/ε ≤ (2:ℝ)^(k+1)) :
    ∃ j : Fin n, ∀ w : EuclideanSpace ℂ (Fin n), ‖w‖=1 →
      ‖L-rankOne ℂ w w‖ ≤ ε/1000 →
        (L^(k+1)) (section5_coordinate_ket j) ≠ 0 ∧
          ∃ ζ : ℂ, ‖ζ‖=1 ∧
            ‖NormedSpace.normalize ((L^(k+1)) (section5_coordinate_ket j))-ζ • w‖ ≤ ε/24 := by sorry
