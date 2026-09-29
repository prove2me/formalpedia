-- Prove2me | Theorems.Thm_harmonic_tail_lt_log
-- name    : harmonic_tail_lt_log
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T19:46:51.051859+00:00
-- url     : https://prove2.me/theorems/2c35b285-563f-4f81-a9e3-4e59d4e8a058
-- title:
--   Strict harmonic-tail upper bound: $\sum_{j=a}^{b-1}\frac1{j+1}<\log\frac ba$
-- statement:
--   **Strict harmonic-vs-log bound.** For naturals $1 \le a < b$, $$\sum_{j=a}^{b-1} \frac{1}{j+1} \;<\; \log\frac{b}{a},$$ equivalently $\sum_{i=a+1}^{b} \frac{1}{i} < \log(b/a) = \int_a^b \frac{dx}{x}$. Proved from the strict per-term inequality $\frac{1}{j+1} < \log\frac{j+1}{j}$ (which follows from $\log x < x-1$ applied at $x=\frac{j}{j+1}<1$) summed against the telescoping identity $\sum_{j=a}^{b-1}\log\frac{j+1}{j} = \log\frac{b}{a}$.
-- source:
--   Standard comparison of the harmonic partial sum with the logarithm (integral test, strict because $1/x$ is strictly decreasing). Used e.g. in Siegel 2001 (J. Algorithms 38:184-236) for $E[T] < 1$ at the homogeneous rate.

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false
open scoped BigOperators
open Finset

theorem harmonic_tail_lt_log (a b : ℕ) (ha : 1 ≤ a) (hab : a < b) :
    (∑ j ∈ Finset.Ico a b, (1 : ℝ) / (j + 1)) < Real.log ((b:ℝ) / a) := by sorry
