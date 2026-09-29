-- Prove2me | Theorems.Thm_WorkbookRestored_plus_11215
-- name    : WorkbookRestored.plus_11215
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:30:10.97188+00:00
-- url     : https://prove2.me/theorems/39c9ef9e-2c57-4d58-b2b1-206385e5c23d
-- title:
--   Lean-Workbook Plus 11215: Trigonometric inequality
-- statement:
--   prove that : $ 3(\cos^2x+\cos^2y+\cos^2z) \geq ( \cos x+ \cos y+ \cos z)^2$
--
--   Source: Lean-Workbook row `lean_workbook_plus_11215` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/aa330e17-9bf4-4ae0-a35a-c7c7dbc46574); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_11215; immutable original Prove2Me node aa330e17-9bf4-4ae0-a35a-c7c7dbc46574

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_11215 (x y z: ℝ) : 3 * (Real.cos x ^ 2 + Real.cos y ^ 2 + Real.cos z ^ 2) ≥ (Real.cos x + Real.cos y + Real.cos z) ^ 2   :=  by sorry
