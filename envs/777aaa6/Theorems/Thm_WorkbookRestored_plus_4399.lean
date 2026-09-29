-- Prove2me | Theorems.Thm_WorkbookRestored_plus_4399
-- name    : WorkbookRestored.plus_4399
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:28:18.572459+00:00
-- url     : https://prove2.me/theorems/f123bd0f-4d7a-40e3-ad40-f2c9197fec68
-- title:
--   Lean-Workbook Plus 4399: Trigonometric identity
-- statement:
--   prove \( \cos 3a = 4\cdot \cos^{3}a - 3\cos a \)
--
--   Source: Lean-Workbook row `lean_workbook_plus_4399` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/30bdaa83-4b38-4a39-8ff5-04a09723b265); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_4399; immutable original Prove2Me node 30bdaa83-4b38-4a39-8ff5-04a09723b265

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_4399 (a : ℝ) : Real.cos (3 * a) = 4 * (Real.cos a)^3 - 3 * Real.cos a   :=  by sorry
