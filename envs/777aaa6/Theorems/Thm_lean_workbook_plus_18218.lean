-- Prove2me | Theorems.Thm_lean_workbook_plus_18218
-- name    : lean_workbook_plus_18218
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/8c5b8e2b-1a8f-4965-a16b-a9897011e51d
-- statement:
--   Prove $(a^2+c^2)(b^2+d^2)(c^2+d^2+a^2+b^2) \ge (abc+bcd+cda+dab)^2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18218 (a b c d : ℝ) : (a^2+c^2)*(b^2+d^2)*(c^2+d^2+a^2+b^2) ≥ (a*b*c+b*c*d+c*d*a+d*a*b)^2   :=  by sorry
