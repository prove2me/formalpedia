-- Prove2me | Theorems.Thm_lean_workbook_plus_55107
-- name    : lean_workbook_plus_55107
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/236ba8f3-34b4-47b5-b15a-c42a7de3f366
-- statement:
--   If $a,b,c$ are positive numbers and $ab+bc+ca=abc$ , prove that $5(a+b+c) \geq 18 +3(ab+bc+ca)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55107 (a b c : ℝ) (h : a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c = a * b + b * c + c * a) : 5 * (a + b + c) ≥ 18 + 3 * (a * b + b * c + c * a)   :=  by sorry
