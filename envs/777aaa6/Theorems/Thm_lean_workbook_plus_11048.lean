-- Prove2me | Theorems.Thm_lean_workbook_plus_11048
-- name    : lean_workbook_plus_11048
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/87ba0db5-8789-4a08-9afe-0324d1811d85
-- statement:
--   We have to prove the inequality $a^2+b^2+c^2+d^2\geq ac+bd+cb+da$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11048 (a b c d : ℝ) : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 ≥ a * c + b * d + c * b + d * a   :=  by sorry
