-- Prove2me | Theorems.Thm_lean_workbook_plus_21474
-- name    : lean_workbook_plus_21474
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/c18abc66-b284-4b31-84cf-5b885a4c768b
-- statement:
--   Prove that $ e^x\geq 1+x$ for $ x\geq 0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21474 (x : ℝ) (hx : 0 ≤ x) : exp x ≥ 1 + x   :=  by sorry
