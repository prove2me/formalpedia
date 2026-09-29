-- Prove2me | Theorems.Thm_lean_workbook_plus_37788
-- name    : lean_workbook_plus_37788
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/f52d40b2-01b2-4bd3-934c-23ef642552a1
-- statement:
--   Show that the inequality is equivalent to $\frac{9}{4} + \cos^2 A + \cos^2 B + \cos ^2 C \ge \cos A + \cos B + \cos C$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37788 {A B C : ℝ} (hA : 0 < A ∧ A ≤ π ∧ B ≤ π ∧ C ≤ π) (hB : 0 < B ∧ B ≤ π ∧ A ≤ π ∧ C ≤ π) (hC : 0 < C ∧ C ≤ π ∧ A ≤ π ∧ B ≤ π) : 9 / 4 + Real.cos A ^ 2 + Real.cos B ^ 2 + Real.cos C ^ 2 ≥ Real.cos A + Real.cos B + Real.cos C   :=  by sorry
