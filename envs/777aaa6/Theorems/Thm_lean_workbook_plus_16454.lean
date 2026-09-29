-- Prove2me | Theorems.Thm_lean_workbook_plus_16454
-- name    : lean_workbook_plus_16454
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/c3afb1e8-3075-4c54-a228-5aaaa111daff
-- statement:
--   Alternatively, you can notice that the sum or product of an odd number of negatives is a negative. All squares must be non-negative. So we know $(x-1)^2$ is always positive (or zero, but that would make it false), so we only have to worry about $\frac{(x-2)}{(x-3)}$ . $x-2$ is positive if $x>2$ and negative if $x<2$ , and $x-3$ is positive if $x>3$ and negative if $x<3$ . We want one of them will be positive and the other will be negative to get a negative quotient. This happens if $2<x<3$ , or $\boxed{(2,3)}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16454  (x : ℝ)
  (h₀ : 0 < (x - 1)^2)
  (h₁ : (x - 2) / (x - 3) < 0) :
  2 < x ∧ x < 3   :=  by sorry
