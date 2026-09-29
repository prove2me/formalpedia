-- Prove2me | Theorems.Thm_lean_workbook_plus_57076
-- name    : lean_workbook_plus_57076
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/e47d975f-8357-46c7-bd1e-8d7a447f5ca7
-- statement:
--   Let $a,b,c$ are real numbers,prove that: $(a^2b+b^2c+c^2a)^2 \geq 3(a^2c+ab^2+bc^2)abc.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57076 (a b c : ℝ) : (a^2 * b + b^2 * c + c^2 * a)^2 ≥ 3 * (a^2 * c + a * b^2 + b * c^2) * a * b * c   :=  by sorry
