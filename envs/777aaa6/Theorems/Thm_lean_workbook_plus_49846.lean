-- Prove2me | Theorems.Thm_lean_workbook_plus_49846
-- name    : lean_workbook_plus_49846
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/5823d939-0b49-49d5-ac7d-24c51c5a43f9
-- statement:
--   prove that $ (x+y+z)^2\ge y(2x+y+2z)$ given $ x,y,z>0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49846 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y + z) ^ 2 ≥ y * (2 * x + y + 2 * z)   :=  by sorry
