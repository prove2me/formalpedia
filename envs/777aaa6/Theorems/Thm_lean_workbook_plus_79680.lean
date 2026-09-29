-- Prove2me | Theorems.Thm_lean_workbook_plus_79680
-- name    : lean_workbook_plus_79680
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/abe714de-8a3c-4e8a-8f0f-4fe3e0e588ca
-- statement:
--   Isn't $2(7x - 2y + xy + 3x + 5xy - 2) = \boxed{12xy + 20x - 4y -4}$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79680 (x y : ℤ) : 2 * (7 * x - 2 * y + x * y + 3 * x + 5 * x * y - 2) = 12 * x * y + 20 * x - 4 * y - 4   :=  by sorry
