-- Prove2me | Theorems.Thm_WorkbookRestored_plus_54215
-- name    : WorkbookRestored.plus_54215
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:16:52.542201+00:00
-- url     : https://prove2.me/theorems/294d3d53-2f79-4023-b98e-54326d8667b7
-- title:
--   Lean-Workbook Plus 54215: Trigonometric identity
-- statement:
--   $\sin 4a = 4 \sin a \cos^{3} a - 4 \cos a \sin^{3} a$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_54215` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/c5c3b7c7-e0bd-4517-8a77-1816f4b3750f); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_54215; immutable original Prove2Me node c5c3b7c7-e0bd-4517-8a77-1816f4b3750f

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_54215 (a : ℝ) : Real.sin (4 * a) = 4 * Real.sin a * (Real.cos a)^3 - 4 * Real.cos a * (Real.sin a)^3   :=  by sorry
