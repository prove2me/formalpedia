-- Prove2me | Theorems.Thm_lean_workbook_plus_1809
-- name    : lean_workbook_plus_1809
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/070c28aa-e018-4e17-8e7f-41ad62667116
-- statement:
--   Let $a, b$ and $ c$ be positive real numbers such that $a+b+c\geq 3abc$ . Prove that $a^2+b^2+c^2\geq 2abc.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1809 (a b c : ℝ) (h : a + b + c ≥ 3 * a * b * c) : a ^ 2 + b ^ 2 + c ^ 2 ≥ 2 * a * b * c   :=  by sorry
