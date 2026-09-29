-- Prove2me | Theorems.Thm_WorkbookRestored_plus_11950
-- name    : WorkbookRestored.plus_11950
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:30:20.689192+00:00
-- url     : https://prove2.me/theorems/c4fc9b06-9966-4a83-986e-e8d28504b8ac
-- title:
--   Lean-Workbook Plus 11950: Trigonometric identity
-- statement:
--   For every real $x$, $\cos(3x)=\cos x\,(1-4\sin^2 x)$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_11950` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/f5d86adc-75b9-4f41-9498-9bcfb0e60a62); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_11950; immutable original Prove2Me node f5d86adc-75b9-4f41-9498-9bcfb0e60a62

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_11950 x : Real.cos (3 * x) = Real.cos x * (1 - 4 * (Real.sin x)^2)   :=  by sorry
