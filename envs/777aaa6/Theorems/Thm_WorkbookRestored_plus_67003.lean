-- Prove2me | Theorems.Thm_WorkbookRestored_plus_67003
-- name    : WorkbookRestored.plus_67003
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:08:45.467833+00:00
-- url     : https://prove2.me/theorems/58ea3560-343d-4ce8-b12a-37b2f7a02bcf
-- title:
--   Lean-Workbook Plus 67003: Comparing reflected square-root distances
-- statement:
--   For $0\le x\le\pi/2$, $\sqrt{1+(\pi-x)^2}-\sqrt{1+x^2}\ge0$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_67003` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/a3978486-7726-4f8a-986b-f8dda2fee828); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_67003; immutable original Prove2Me node a3978486-7726-4f8a-986b-f8dda2fee828

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_67003 (x : ℝ) (hx : 0 ≤ x ∧ x ≤ π/2) : 0 ≤ Real.sqrt (1 + (π - x) ^ 2) - Real.sqrt (1 + x ^ 2)   :=  by sorry
