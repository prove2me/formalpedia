-- Prove2me | Theorems.Thm_lean_workbook_plus_68549
-- name    : lean_workbook_plus_68549
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/a39386ef-6dcc-4884-83ef-ff375e9df1e1
-- statement:
--   Prove that \((a^2+b^2)(a^4+b^2c^2)\geq a^2b^2(c+a)^2\) given \(a, b, c>0\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68549 (a b c : ℝ) (habc : a * b * c > 0) : (a^2 + b^2) * (a^4 + b^2 * c^2) ≥ a^2 * b^2 * (c + a)^2   :=  by sorry
