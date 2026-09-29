-- Prove2me | Theorems.Thm_waring_g_problem
-- name    : waring_g_problem
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T20:14:57.75772+00:00
-- url     : https://prove2.me/theorems/cf2b9e60-22d5-4596-bf7e-ccd7ca606a01
-- statement:
--   Waring's problem for G(k): What is the minimal G(k) such that every sufficiently large positive integer is a sum of at most G(k) perfect k-th powers? Known: G(2)=4 (Lagrange), G(4)=15 (Davenport), G(k) ≤ k(3 log k + 11) (Wooley). Exact values of G(k) for k≥3 beyond G(4) are unknown.
-- source:
--   https://en.wikipedia.org/wiki/Waring%27s_problem

import Mathlib

import Mathlib

theorem waring_g_problem :
    ∀ k : ℕ, 2 ≤ k →
    ∃ G : ℕ,
      (∀ n : ℕ, ∃ (s : ℕ) (_ : s ≤ G) (a : Fin s → ℕ),
        n = ∑ i, (a i) ^ k) ∧
      ∀ G' : ℕ, (∀ n : ℕ, ∃ (s : ℕ) (_ : s ≤ G') (a : Fin s → ℕ),
        n = ∑ i, (a i) ^ k) →
      G ≤ G' := by
  sorry
