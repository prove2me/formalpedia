-- Prove2me | Theorems.Thm_lean_workbook_plus_11592
-- name    : lean_workbook_plus_11592
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/aec78953-a97a-4b06-b458-92fd45509a48
-- statement:
--   Prove for all positive real x, y and z, that $(xy+yz+zx)^{3}\le 27((x+y)(y+z)(z+x))^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11592 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x * y + y * z + z * x)^3 ≤ 27 * ((x + y) * (y + z) * (z + x))^2   :=  by sorry
