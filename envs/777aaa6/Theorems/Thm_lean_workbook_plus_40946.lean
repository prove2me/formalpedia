-- Prove2me | Theorems.Thm_lean_workbook_plus_40946
-- name    : lean_workbook_plus_40946
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/a1b55943-f449-4d64-8bf0-3d777428ff46
-- statement:
--   If $a > 0,b > 0,c > 0$ and $a \cdot b \cdot c = 1$ , to prove that: $a^4 + b^4 + c^4 \geqslant a + b + c$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40946 (a b c : ℝ) (h : a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c = 1): a^4 + b^4 + c^4 ≥ a + b + c   :=  by sorry
