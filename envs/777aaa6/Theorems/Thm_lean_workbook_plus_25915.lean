-- Prove2me | Theorems.Thm_lean_workbook_plus_25915
-- name    : lean_workbook_plus_25915
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/5b0939c3-f9e4-4b8d-851e-7c9d4e9e1801
-- statement:
--   Prove that for all real non-zero numbers a, b, c, ab + bc + ca ≤ $a^2 + b^2 + c^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25915 (a b c : ℝ) (habc : a * b * c ≠ 0) : a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2   :=  by sorry
