-- Prove2me | Theorems.Thm_gpy_mertensMuSqSum_abel
-- name    : gpy_mertensMuSqSum_abel
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T19:30:58.075584+00:00
-- url     : https://prove2.me/theorems/6ab758b5-e2dc-4a3c-a002-d8b59c6e91a9
-- title:
--   Abel transform of the mu-squared-over-phi log-power sum
-- statement:
--   For a natural number $m$ and a bound $T$, let the one-variable Mertens-type sum be $S(m, T) = \sum_{D \leq T} w(D) (\log D)^m$, where $w(D) = \mu(D)^2 / \varphi(D)$ when $D$ is squarefree and $0$ otherwise (the square of the Möbius value is the squarefree indicator). Then summation by parts gives
--
--   $$S(m, T) = \left(\sum_{D \leq T} w(D)\right) (\log T)^m - \sum_{i < T} \left(\sum_{D \leq i} w(D)\right) \big((\log (i+1))^m - (\log i)^m\big).$$
--
--   This is the exact entry point for Mertens-type estimates: they bound the partial sums $\sum_{D \leq i} w(D)$, and Abel summation converts those bounds into bounds on the log-power sums. Formalization Note: the weight and the sum are unfolded into explicit range sums with the squarefree condition inline.
-- source:
--   GPY conditional monomial evaluation: the Abel transform of the one-variable mu-squared-over-phi log-power sum, directly from summation by parts

import Mathlib
open Classical

theorem gpy_mertensMuSqSum_abel (m : ℕ) (T : ℕ) :
    (∑ D ∈ Finset.range (T + 1),
      (if Squarefree D then (ArithmeticFunction.moebius D : ℝ) ^ 2
        / ((Nat.totient D : ℕ) : ℝ) else 0) * (Real.log (D : ℝ)) ^ m)
      = (∑ D ∈ Finset.range (T + 1),
          (if Squarefree D then (ArithmeticFunction.moebius D : ℝ) ^ 2
            / ((Nat.totient D : ℕ) : ℝ) else 0)) * (Real.log (T : ℝ)) ^ m
        - ∑ i ∈ Finset.range T,
            (∑ D ∈ Finset.range (i + 1),
              (if Squarefree D then (ArithmeticFunction.moebius D : ℝ) ^ 2
                / ((Nat.totient D : ℕ) : ℝ) else 0))
              * ((Real.log ((i + 1 : ℕ) : ℝ)) ^ m - (Real.log (i : ℝ)) ^ m) := by sorry
