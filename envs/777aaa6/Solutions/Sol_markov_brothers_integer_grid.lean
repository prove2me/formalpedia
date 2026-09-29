-- Prove2me | solution 1 for markov_brothers_integer_grid
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-05-09T00:51:05.957362+00:00
-- url     : https://prove2.me/submissions/5d248079-1ec3-428c-882c-a8715b59f52e

import Theorems.Thm_markov_brothers_integer_grid
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs

open Polynomial

/-- Disproof of `markov_brothers_integer_grid`.

Counterexample: `b = 1`, `Q = 10·X² − 10·X`, `d = 2`, `c = 0`.
Then `Q(0) = Q(1) = 0` so the grid bound `|Q(t)| ≤ 1` holds, and
`natDegree Q = 2 ≤ 2`, but `Q'(x) = 20X − 10` so `|Q'(0)| = 10 > 8 = 2·d²/b`.

The theorem is false because the hypothesis only controls `Q` at the integer
grid points, which does not pin down its behavior between grid points when
`d` exceeds the number of grid intervals. -/
theorem solution : ¬ markov_brothers_integer_grid := by
  intro h
  -- Apply h at b = 1, Q = C 10 * X^2 - C 10 * X, d = 2, c = 0.
  have key := @h 1 (le_refl 1) (C (10 : ℝ) * X ^ 2 - C (10 : ℝ) * X) 2
    (by compute_degree)
    (by
      intro t ht
      interval_cases t <;>
        simp only [Nat.cast_zero, Nat.cast_one, eval_sub, eval_mul, eval_C, eval_pow, eval_X] <;>
        norm_num)
    0 le_rfl (by norm_num)
  -- key : |derivative (C 10 * X^2 - C 10 * X) .eval 0| ≤ 2 * (2:ℝ)^2 / (1:ℝ)
  -- derivative = C 10 * (C 2 * X) - C 10 * 1 = C 20 * X - C 10, eval at 0 = -10
  simp only [derivative_sub, derivative_C_mul, derivative_X_pow, derivative_X,
    eval_sub, eval_mul, eval_C, eval_pow, eval_X, eval_one,
    Nat.cast_ofNat, Nat.cast_one, pow_one, mul_one, mul_zero, zero_sub] at key
  -- key : |(-10 : ℝ)| ≤ 2 * 2 ^ 2 / 1
  norm_num at key
