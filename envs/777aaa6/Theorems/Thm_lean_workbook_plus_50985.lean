-- Prove2me | Theorems.Thm_lean_workbook_plus_50985
-- name    : lean_workbook_plus_50985
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/68204143-6fed-4071-86f7-7c6eda682331
-- statement:
--   For $x > -1$ , we have $\ln (1 + x) \leq x$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50985 (x : ℝ) (hx : -1 < x) : Real.log (1 + x) ≤ x   :=  by sorry
