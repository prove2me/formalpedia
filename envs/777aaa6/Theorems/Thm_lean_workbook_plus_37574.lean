-- Prove2me | Theorems.Thm_lean_workbook_plus_37574
-- name    : lean_workbook_plus_37574
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/51df94fb-acdc-4caa-9bd7-2702b28b06bc
-- statement:
--   Prove for all $x,y,z \in R$ , the following multivariable inequality holds: $(x+y)^{2}+(y+z)^{2}+(z+x)^{2}\ge \frac{4(x+y+z)^{2}}{3} $ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37574 (x y z : ℝ) : (x + y) ^ 2 + (y + z) ^ 2 + (z + x) ^ 2 ≥ (4 * (x + y + z) ^ 2)/3   :=  by sorry
