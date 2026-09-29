-- Prove2me | Theorems.Thm_WorkbookRestored_plus_51489
-- name    : WorkbookRestored.plus_51489
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:04:12.183636+00:00
-- url     : https://prove2.me/theorems/f7b7ae3f-dd8b-4248-b428-56222e5f171b
-- title:
--   Lean-Workbook Plus 51489: Logarithmic inequality
-- statement:
--   For real $a>1$, $1-1/a-\log a<0$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_51489` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/edabfb75-5508-4ad6-a5fe-a27f3852ca46); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_51489; immutable original Prove2Me node edabfb75-5508-4ad6-a5fe-a27f3852ca46

import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real

theorem WorkbookRestored.plus_51489 (a : ℝ) (ha : 1 < a) : 1 - (1 / a) - Real.log a < 0   :=  by sorry
