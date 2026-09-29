-- Prove2me | Theorems.Thm_lean_workbook_plus_51490
-- name    : lean_workbook_plus_51490
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/054df698-4caa-4187-9c96-1c8a17e1638c
-- statement:
--   Solve diff. equation $xy'-y=x\sin x$ over interval $(-\infty,\infty)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51490 (x : ℝ) : ∃ y, x * y' - y = x * Real.sin x   :=  by sorry
