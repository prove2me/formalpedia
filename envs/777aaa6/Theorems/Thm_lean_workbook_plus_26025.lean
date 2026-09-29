-- Prove2me | Theorems.Thm_lean_workbook_plus_26025
-- name    : lean_workbook_plus_26025
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/f3d980dc-a285-4a27-bcba-9624bc8d4547
-- statement:
--   Let $x$ be the number of students in both clubs. Then, there are $11 + x$ total people. This is also equal to $15 + 12 - x$ . So $27 - x = 11 + x \Longrightarrow x = \boxed{8}$ people. $\boxed{\textbf{(C)}}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26025  (x : ℕ)
  (h₀ : 0 < x)
  (h₁ : 11 + x = 15 + 12 - x) :
  x = 8   :=  by sorry
