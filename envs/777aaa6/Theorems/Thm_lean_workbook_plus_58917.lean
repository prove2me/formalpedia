-- Prove2me | Theorems.Thm_lean_workbook_plus_58917
-- name    : lean_workbook_plus_58917
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/ec5ced54-c28c-492d-9c44-9a64b4176e93
-- statement:
--   After expand, the inequality become \n\n $4\left[x^2y^2+y^2z^2+z^2x^2-xyz(x+y+z)\right] \geqslant 0,$ or \n\n $3z^2(x-y)^2+(2xy-xz-yz)^2 \geqslant 0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58917 (x y z : ℝ) :
  4 * (x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2 - x * y * z * (x + y + z)) ≥ 0   :=  by sorry
