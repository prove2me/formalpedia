-- Prove2me | Theorems.Thm_dirichlet_divisor_problem
-- name    : dirichlet_divisor_problem
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-06-01T02:35:49.220247+00:00
-- url     : https://prove2.me/theorems/80926ede-f5e7-4bc1-8273-c685a550f7d5
-- statement:
--   Dirichlet divisor problem: Error in ∑_{n≤x} d(n) ~ x log x is O(x^{1/4+ε}). Best known O(x^{131/416}) (Huxley). Exponent 1/4 conjectured by Cramér; same as Gauss circle problem.
-- source:
--   https://en.wikipedia.org/wiki/Divisor_summatory_function

import Mathlib

import Mathlib

theorem dirichlet_divisor_problem :
    ∀ eps : ℝ, 0 < eps →
    ∃ C : ℝ, 0 < C ∧
    ∀ x : ℝ, 1 ≤ x →
      |(∑ k ∈ Finset.Icc 1 (Nat.floor x), (Nat.divisors k).card : ℝ) -
       (x * Real.log x + (2 * Real.eulerMascheroniConstant - 1) * x)| ≤
      C * x ^ (1/4 + eps) := by
  sorry
