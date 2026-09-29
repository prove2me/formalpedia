-- Prove2me | Theorems.Thm_lean_workbook_plus_40040
-- name    : lean_workbook_plus_40040
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/0e3e3ab4-8181-4bf3-aa94-06cb1d955dd4
-- statement:
--   If $a \geq b \geq c$ , prove that $(a+c)^2\geq ab+bc+ca$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40040 (a b c : ℝ) (hab : a ≥ b) (hbc : b ≥ c) : (a + c) ^ 2 ≥ a * b + b * c + c * a   :=  by sorry
