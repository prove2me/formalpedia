-- Prove2me | Theorems.Thm_WorkbookRestored_plus_25895
-- name    : WorkbookRestored.plus_25895
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:00:35.115981+00:00
-- url     : https://prove2.me/theorems/40aa66e3-42f8-43ba-8914-b0da2d9a6744
-- title:
--   Lean-Workbook Plus 25895: Trigonometric identity
-- statement:
--   If $\cos x-\cos y=1/5$, then $-2\sin((x+y)/2)\sin((x-y)/2)=1/5$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_25895` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/bdae1187-3ea3-4b55-809e-83be3c57be82); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_25895; immutable original Prove2Me node bdae1187-3ea3-4b55-809e-83be3c57be82

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_25895 (x y : ℝ) (h : cos x - cos y = 1 / 5) :
  -2 * sin ((x + y) / 2) * sin ((x - y) / 2) = 1 / 5   :=  by sorry
