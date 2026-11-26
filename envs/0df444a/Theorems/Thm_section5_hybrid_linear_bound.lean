-- Prove2me | Theorems.Thm_section5_hybrid_linear_bound
-- name    : section5_hybrid_linear_bound
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:48:37.903234+00:00
-- url     : https://prove2.me/theorems/ecd1eb36-f595-5f68-8bc0-0490fa8af86d
-- title:
--   Linear bound for a small product perturbation
-- statement:
--   Let n be natural and δ≥0 real with nδ≤1/2. Then $$(1+\delta)^n-1\le2n\delta.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5. Exact formalization: Solutions/Section5ProductSampling.lean, lines 302–303. Analytic context: Section 5.1, Lemma 5.1 and Appendix D; this auxiliary formulation does not assert the main quantum learning algorithm.

import Mathlib
set_option autoImplicit false
open MeasureTheory

theorem section5_hybrid_linear_bound (n : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hsmall : (n:ℝ)*δ ≤ 1/2) : (1+δ)^n-1 ≤ 2*n*δ := by sorry
