-- Prove2me | Theorems.Thm_lean_workbook_plus_61182
-- name    : lean_workbook_plus_61182
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/a8812f45-ae50-4814-8d89-e1056ebffa2a
-- statement:
--   Let $a+b+c=3$ , and a,b, and c are positive real number, prove that $a^2 + b^2 + c^2 \geq a + b + c$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61182 (a b c : ℝ) (hab : a + b + c = 3) (h : a > 0 ∧ b > 0 ∧ c > 0)(habc : a * b * c = 1) : a ^ 2 + b ^ 2 + c ^ 2 ≥ a + b + c   :=  by sorry
