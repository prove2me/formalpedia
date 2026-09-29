-- Prove2me | Theorems.Thm_lean_workbook_plus_29898
-- name    : lean_workbook_plus_29898
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/c1206278-a9b8-4c22-937c-e7c0bfffbbc5
-- statement:
--   Prove that for any $ x > 0$ , then \n $ 2x^4-7x^3+12x+ 2 > 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29898 (x : ℝ) (hx : 0 < x) : 2 * x^4 - 7 * x^3 + 12 * x + 2 > 0   :=  by sorry
