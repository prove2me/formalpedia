-- Prove2me | Theorems.Thm_WorkbookRestored_plus_60372
-- name    : WorkbookRestored.plus_60372
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:17:19.574601+00:00
-- url     : https://prove2.me/theorems/dd9c52ea-e007-4ff9-badf-58606c444d74
-- title:
--   Lean-Workbook Plus 60372: Trigonometric identity
-- statement:
--   $2\sin x\cos y=\sin (x+y)+\sin(x-y)$
--
--   Source: Lean-Workbook row `lean_workbook_plus_60372` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/cd16c49c-67d3-4a78-a879-e752e3900f01); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_60372; immutable original Prove2Me node cd16c49c-67d3-4a78-a879-e752e3900f01

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_60372 : ∀ x y : ℝ, 2 * sin x * cos y = sin (x + y) + sin (x - y)   :=  by sorry
