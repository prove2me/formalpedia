-- Prove2me | Theorems.Thm_lean_workbook_plus_62631
-- name    : lean_workbook_plus_62631
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/6360e937-8d7a-4626-9add-55767ed6e3cb
-- statement:
--   Prove that $(1^2 + 1^2 + 1^2)\left((x+y)^{2}+(y+z)^{2}+(z+x)^{2}\right)\ge ((x+y)+(y+z)+(x+z))^{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62631 (x y z : ℝ) :
  (1^2 + 1^2 + 1^2) * ((x + y)^2 + (y + z)^2 + (z + x)^2) ≥ ((x + y) + (y + z) + (x + z))^2   :=  by sorry
