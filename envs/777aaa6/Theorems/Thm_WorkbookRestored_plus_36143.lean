-- Prove2me | Theorems.Thm_WorkbookRestored_plus_36143
-- name    : WorkbookRestored.plus_36143
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:02:08.544775+00:00
-- url     : https://prove2.me/theorems/dd6e6514-bdc5-4b8d-944f-1a814d8573ea
-- title:
--   Lean-Workbook Plus 36143: Logarithmic inequality
-- statement:
--   For real $a$ and $x>0$, $a\log x=\log(x^a)$, with real exponentiation. This is the first identity in the source.
--
--   Source: Lean-Workbook row `lean_workbook_plus_36143` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/940879bb-cdcb-44e1-bdbe-818401839e7d); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_36143; immutable original Prove2Me node 940879bb-cdcb-44e1-bdbe-818401839e7d

import Mathlib.Analysis.SpecialFunctions.Log.Base
open Real

theorem WorkbookRestored.plus_36143 (a x : ℝ) (h₁ : x > 0) : a * Real.log x = Real.log (x ^ a)   :=  by sorry
