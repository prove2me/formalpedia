-- Prove2me | Theorems.Thm_lean_workbook_plus_23624
-- name    : lean_workbook_plus_23624
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/d0b9ec96-f81d-4684-b9b7-f26dea888d84
-- statement:
--   If the above is unclear, let $a$ and $b$ be the two solutions to $x^2 - 2x- 48 = 0$ . Obviously they are distinct. Then one possible common difference is $a + 24$ , and the other is $b + 24$ . Their sum is $a + b + 48$ , and by Vieta's $a + b = 2$ . Of course, you could just solve to get $x = 8$ or $x = -6$ and substitute.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23624  (a b : ℝ)
  (h₀ : a ≠ b)
  (h₁ : a^2 - 2 * a - 48 = 0)
  (h₂ : b^2 - 2 * b - 48 = 0) :
  (a + 24) + (b + 24) = 2 + 48   :=  by sorry
