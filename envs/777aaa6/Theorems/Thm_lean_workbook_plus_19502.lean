-- Prove2me | Theorems.Thm_lean_workbook_plus_19502
-- name    : lean_workbook_plus_19502
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/1ed989b1-4929-427a-aef8-56831f70e77f
-- statement:
--   prove that $(a+b+c)^{2}\geq 3(ab+bc+ca)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19502 {a b c : ℝ} : (a + b + c) ^ 2 ≥ 3 * (a * b + b * c + c * a)   :=  by sorry
