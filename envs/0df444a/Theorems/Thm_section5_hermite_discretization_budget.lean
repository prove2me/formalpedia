-- Prove2me | Theorems.Thm_section5_hermite_discretization_budget
-- name    : section5_hermite_discretization_budget
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:21:57.500206+00:00
-- url     : https://prove2.me/theorems/3aab8c4a-0843-4d81-b099-11ebfccf214d
-- title:
--   Explicit half-budget for the Hermite discretization error
-- statement:
--   Let n,D,M,η be real with n≥0, D+1≥0, M>0 and η>0. Suppose M≥20736n²(D+1)/η², M≥165888n/η⁴ and M≥(4/π)log(12√(2n)/η). Then $$24n\sqrt{(D+1)/M}+2(8n/M)^{1/4}+2\sqrt{2n}e^{-\pi M/4}\le\eta/2.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5. Exact formalization: Solutions/Section5HermiteErrorBudget.lean, lines 5–11.

import Mathlib
set_option autoImplicit false

theorem section5_hermite_discretization_budget (n D M η : ℝ)
    (hn : 0 ≤ n) (hD : 0 ≤ D+1) (hM : 0 < M) (hη : 0 < η)
    (h1 : 20736*n^2*(D+1)/η^2 ≤ M)
    (h2 : 165888*n/η^4 ≤ M)
    (h3 : 4/Real.pi * Real.log (12*Real.sqrt (2*n)/η) ≤ M) :
    24*n*Real.sqrt ((D+1)/M) + 2*(8*n/M)^(1/4:ℝ) +
      2*Real.sqrt (2*n)*Real.exp (-Real.pi*M/4) ≤ η/2 := by sorry
