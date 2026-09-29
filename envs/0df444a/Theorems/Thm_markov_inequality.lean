-- Prove2me | Theorems.Thm_markov_inequality
-- name    : markov_inequality
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T13:17:08.065335+00:00
-- url     : https://prove2.me/theorems/a92babab-c09e-45b2-ac18-fb62e1c2db11
-- statement:
--   Markov brothers inequality: If |f(x)| ≤ 1 on [-1,1] for a polynomial f of degree n, then |f'(x)| ≤ n² on [-1,1]. Proved by Andrei Markov (1889). Sharp with equality at Chebyshev polynomials.
-- source:
--   https://en.wikipedia.org/wiki/Markov_brothers%27_inequality

import Mathlib

import Mathlib

theorem markov_inequality (f : ℝ → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hf : ∀ x, |x| ≤ 1 → |f x| ≤ 1)
    (hpoly : ∃ p : Polynomial ℝ, p.natDegree = n ∧ ∀ x, p.eval x = f x) :
    ∀ x : ℝ, |x| ≤ 1 → |deriv f x| ≤ n ^ 2 := by
  sorry
