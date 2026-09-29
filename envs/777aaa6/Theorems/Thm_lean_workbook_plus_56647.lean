-- Prove2me | Theorems.Thm_lean_workbook_plus_56647
-- name    : lean_workbook_plus_56647
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/fe19a096-3b30-4828-8cda-c47cfdcac2ff
-- statement:
--   For all reals $a,b,c$ , prove that: $5a^2+8b^2+9c^2\ge 4ab+12bc+6ca$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56647 (a b c : ℝ) : 5 * a ^ 2 + 8 * b ^ 2 + 9 * c ^ 2 ≥ 4 * a * b + 12 * b * c + 6 * c * a   :=  by sorry
