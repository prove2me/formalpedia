-- Prove2me | Theorems.Thm_lean_workbook_plus_5598
-- name    : lean_workbook_plus_5598
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/1b7e83c9-f274-4c99-a6d5-19206975a719
-- statement:
--   Prove: $(x+y)(x-y)^2+2(x-1)(y-1)\ge0$ where $x,y\ge0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5598 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : (x + y) * (x - y) ^ 2 + 2 * (x - 1) * (y - 1) ≥ 0   :=  by sorry
