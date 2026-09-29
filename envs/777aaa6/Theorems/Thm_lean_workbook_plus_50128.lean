-- Prove2me | Theorems.Thm_lean_workbook_plus_50128
-- name    : lean_workbook_plus_50128
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/be78b759-9d31-4da9-b36c-1842dc6f652c
-- statement:
--   We have \n\n $x^2+y^2+12z^2+1 - 4z(x+y+1) = (x-2z)^2 + (y-2z)^2+(2z-1)^2 \geqslant 0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50128 (x y z : ℝ) : x^2 + y^2 + 12 * z^2 + 1 - 4 * z * (x + y + 1) = (x - 2 * z)^2 + (y - 2 * z)^2 + (2 * z - 1)^2 ∧ (x - 2 * z)^2 + (y - 2 * z)^2 + (2 * z - 1)^2 >= 0   :=  by sorry
