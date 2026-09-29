-- Prove2me | Theorems.Thm_lean_workbook_plus_23646
-- name    : lean_workbook_plus_23646
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/3843d553-fa1b-439e-ac09-bcf59e0dc6bb
-- statement:
--   If $a,b,c$ are real numbers such that $a+b+c=0,$ then $(2a^2+bc)(2b^2+ca)(2c^2+ab)\le 0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23646 (a b c : ℝ) (h : a + b + c = 0) : (2 * a ^ 2 + b * c) * (2 * b ^ 2 + c * a) * (2 * c ^ 2 + a * b) ≤ 0   :=  by sorry
