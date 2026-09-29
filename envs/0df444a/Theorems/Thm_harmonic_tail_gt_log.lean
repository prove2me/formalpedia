-- Prove2me | Theorems.Thm_harmonic_tail_gt_log
-- name    : harmonic_tail_gt_log
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T20:31:55.436437+00:00
-- url     : https://prove2.me/theorems/c6f05475-7190-415d-9d1e-e08f249f66ad
-- title:
--   Strict harmonic-tail lower bound: $\log\frac{b+1}{a+1}<\sum_{j=a}^{b-1}\frac1{j+1}$
-- statement:
--   **Strict harmonic-tail lower bound.** For naturals $a<b$, $$\log\frac{b+1}{a+1} < \sum_{j=a}^{b-1}\frac1{j+1}.$$ This is the lower companion of `harmonic_tail_lt_log`. Per term, $\log\frac{j+2}{j+1}=\log\!\big(1+\tfrac1{j+1}\big)<\tfrac1{j+1}$ (since $\log(1+x)<x$ for $x>0$), and the left sides telescope to $\log\frac{b+1}{a+1}$.
-- source:
--   Standard harmonic-vs-logarithm inequality (log(1+x)<x), telescoped; companion of the upper bound used in Siegel 2001 median proof for E[T]<1 / the φ' mean condition.

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals
open scoped BigOperators
open Finset

theorem harmonic_tail_gt_log (a b : ℕ) (hab : a < b) : Real.log (((b:ℝ)+1) / (a+1)) < (∑ j ∈ Finset.Ico a b, (1 : ℝ) / (j + 1)) := by sorry
