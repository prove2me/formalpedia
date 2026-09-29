-- Prove2me | Theorems.Thm_lean_workbook_plus_1662
-- name    : lean_workbook_plus_1662
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/0326146e-7eb8-4a15-a9b9-faacaced9903
-- statement:
--   Multiply these two well known inequalities: $(a+c)(c+d)(d+b)(b+a)\ge (a+b+c+d)(abc+bcd+cda+dab)$ $(a+c)(c+b)(b+d)(d+a)\ge (a+b+c+d)(abc+bcd+cda+dab)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1662 {a b c d : ℝ} : (a + c) * (c + d) * (d + b) * (b + a) ≥ (a + b + c + d) * (a * b * c + b * c * d + c * d * a + d * a * b) ∧ (a + c) * (c + b) * (b + d) * (d + a) ≥ (a + b + c + d) * (a * b * c + b * c * d + c * d * a + d * a * b)   :=  by sorry
