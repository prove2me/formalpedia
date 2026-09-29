-- Prove2me | Theorems.Thm_lean_workbook_plus_68586
-- name    : lean_workbook_plus_68586
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/161f9739-b32b-4e2d-9834-49f1c0126f3f
-- statement:
--   Find the value of the expression $5x^4 + 7x^3 + 8x^2 + 9x + 10$ when $x = 1.98$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68586 (x : ℝ) (hx : x = 1.98) : 5 * x ^ 4 + 7 * x ^ 3 + 8 * x ^ 2 + 9 * x + 10 = 190.3676248   :=  by sorry
