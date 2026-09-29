-- Prove2me | Theorems.Thm_lean_workbook_plus_8256
-- name    : lean_workbook_plus_8256
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/0f428416-e64a-440a-8290-7d95a2940e97
-- statement:
--   We know if $ a>b>c>d,$ then $ ad+bc<ac+bd<ab+cd $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8256 (a b c d : ℝ) (h1 : a > b ∧ b > c ∧ c > d) : a * d + b * c < a * c + b * d ∧ a * c + b * d < a * b + c * d   :=  by sorry
