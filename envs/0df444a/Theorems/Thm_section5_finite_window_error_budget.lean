-- Prove2me | Theorems.Thm_section5_finite_window_error_budget
-- name    : section5_finite_window_error_budget
-- status  : Open
-- author  : @stockfish-soup
-- created : 2026-11-26T19:48:35.898953+00:00
-- url     : https://prove2.me/theorems/276e2b15-7643-5f7e-a611-c53846469abd
-- title:
--   Explicit finite-window probability budget
-- statement:
--   Let real n,M,L,ζ satisfy n≥1, M≥1073741824n², L≥32n, ζ≥0 and ζn≤1/512. Then $$\sqrt{8n/M}+2ne^{-L^2/2}+\frac{2\zeta\sqrt n}{\sqrt{2\pi}}+8n\sqrt{32/M}+4\sqrt{2n}e^{-\pi M/4}\le1/32.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5WindowErrorBudget.lean, lines 64–68.

import Mathlib
set_option autoImplicit false

theorem section5_finite_window_error_budget (n M L ζ : ℝ) (hn : 1 ≤ n)
    (hM : 1073741824*n^2 ≤ M) (hL : 32*n ≤ L) (hζ : 0 ≤ ζ) (hsmall : ζ*n ≤ 1/512) :
    Real.sqrt (8*n/M)+2*n*Real.exp (-L^2/2)+
      2*(ζ*Real.sqrt n)/Real.sqrt (2*Real.pi)+
      (8*n*Real.sqrt (32/M)+4*Real.sqrt (2*n)*Real.exp (-Real.pi*M/4)) ≤ 1/32 := by sorry
