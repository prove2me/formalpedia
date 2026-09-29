-- Prove2me | Theorems.Thm_WorkbookRestored_plus_19668
-- name    : WorkbookRestored.plus_19668
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:31:12.754457+00:00
-- url     : https://prove2.me/theorems/36d13b85-43ed-4c2c-a223-44c0a2c57ffa
-- title:
--   Lean-Workbook Plus 19668: Trigonometric identity
-- statement:
--   For all real $x,y$, $\cos x-\cos y=-2\sin((x+y)/2)\sin((x-y)/2)$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_19668` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/445b5f01-4bc3-4eae-96c4-4790a6ff0cd8); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_19668; immutable original Prove2Me node 445b5f01-4bc3-4eae-96c4-4790a6ff0cd8

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_19668 : ∀ x y : ℝ, Real.cos x - Real.cos y = -2 * Real.sin ((x + y) / 2) * Real.sin ((x - y) / 2)   :=  by sorry
