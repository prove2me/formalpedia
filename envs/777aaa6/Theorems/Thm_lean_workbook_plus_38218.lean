-- Prove2me | Theorems.Thm_lean_workbook_plus_38218
-- name    : lean_workbook_plus_38218
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/6513e108-80bd-40d2-bc5f-3052ab8c2772
-- statement:
--   Note that $x^{n+1}\le x^n, x\in [0,1].$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38218 (x : ℝ) (n : ℕ) : x ∈ Set.Icc 0 1 → x ^ (n + 1) ≤ x ^ n   :=  by sorry
