-- Prove2me | Theorems.Thm_lean_workbook_plus_52468
-- name    : lean_workbook_plus_52468
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/4a4e096d-aab4-4933-9277-7c27d30c9467
-- statement:
--   Prove that for any $ x > 0$ , then \n $ 2x^4 + 12x^3 - 7x + 2 > 0.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52468 (x : ℝ) (hx : 0 < x) : 2 * x^4 + 12 * x^3 - 7 * x + 2 > 0   :=  by sorry
