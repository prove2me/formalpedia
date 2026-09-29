-- Prove2me | Theorems.Thm_lean_workbook_plus_26636
-- name    : lean_workbook_plus_26636
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/38baa84e-75d4-4a60-b30c-b9808a31e71e
-- statement:
--   Prove that $ lnx\leq x-1$ for all x > 0.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26636 (x : ℝ) (hx : 0 < x) : Real.log x ≤ x - 1   :=  by sorry
