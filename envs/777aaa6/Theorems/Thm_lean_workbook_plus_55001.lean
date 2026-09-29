-- Prove2me | Theorems.Thm_lean_workbook_plus_55001
-- name    : lean_workbook_plus_55001
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/a387ebec-79d8-4123-a169-c55751c12400
-- statement:
--   Prove that $\frac{a}{(a + 1)(b + 1)} +\frac{ b}{(b + 1)(c + 1)} + \frac{c}{(c + 1)(a + 1)} \ge \frac34$ where $a, b$ and $c$ are positive real numbers satisfying $abc = 1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55001 (a b c : ℝ) (ha : a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c = 1) : (a / (a + 1) * b + 1) + (b / (b + 1) * c + 1) + (c / (c + 1) * a + 1) ≥ 3 / 4   :=  by sorry
