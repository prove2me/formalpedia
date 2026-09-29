-- Prove2me | solution 2 for markov_polya_grid
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-05-09T02:37:18.018122+00:00
-- url     : https://prove2.me/submissions/f333eb67-0585-454e-942a-fe1048e7be09

import Theorems.Thm_markov_polya_grid
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs

open Polynomial

/-- Disproof of `markov_polya_grid`.

Counterexample: `b = 9`, `d = 2`, `Q = X²/10 − 9X/10 + 1`, `c = 0`.

`Q` is the degree-2 Lagrange interpolant through `(0,1), (4,−1), (9,1)`; on the
integer grid `{0,…,9}` its values are `1, 0.2, −0.4, −0.8, −1, −1, −0.8, −0.4,
0.2, 1`, all in `[−1,1]`. The regime hypothesis `2·d² = 8 ≤ 9 = b` holds. But
`Q'(x) = (2x − 9)/10`, so `|Q'(0)| = 9/10 > 8/9 = 2·d²/b`.

The continuous Markov bound `2d²/b` is achieved by Chebyshev polynomials that
are extremal subject to being bounded on *all* of `[0,b]`; a polynomial only
constrained at integer points can have a slightly larger derivative. The
Ehlich–Zeller / Coppersmith–Rivlin continuous extension constant is strictly
greater than `1` even in the regime `2d² ≤ b`, so the claimed bound with
constant `2` is too strong. -/
theorem solution : ¬ markov_polya_grid := by
  intro h
  have key := @h 9 (by norm_num) (C (10 : ℝ)⁻¹ * X ^ 2 - C (9 / 10 : ℝ) * X + C 1) 2
    (by compute_degree)
    (by
      intro t ht
      interval_cases t <;>
        simp only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, eval_add, eval_sub, eval_mul,
          eval_pow, eval_C, eval_X] <;>
        norm_num)
    (by norm_num)
    0 le_rfl (by norm_num)
  simp only [derivative_add, derivative_sub, derivative_mul, derivative_C_mul, derivative_X_pow,
    derivative_X, derivative_C, eval_add, eval_sub, eval_mul, eval_C, eval_pow, eval_X,
    eval_zero, eval_one, Nat.cast_ofNat, Nat.cast_one, mul_zero, zero_mul, mul_one, zero_add,
    add_zero, sub_zero, pow_one, zero_sub, map_ofNat] at key
  norm_num at key
