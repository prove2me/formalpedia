-- Prove2me | Theorems.Thm_WorkbookRestored_plus_9408
-- name    : WorkbookRestored.plus_9408
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:30:08.985311+00:00
-- url     : https://prove2.me/theorems/8cb3a58e-3b7c-454a-aa9b-2db286996357
-- title:
--   Lean-Workbook Plus 9408: Logarithmic inequality
-- statement:
--   If $x>0$ and $x\ne1$, then $x^{\log 30/\log x}=30$, where the exponent is real.
--
--   Source: Lean-Workbook row `lean_workbook_plus_9408` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/ddc40de1-4754-47b3-a386-987cf13ed947); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_9408; immutable original Prove2Me node ddc40de1-4754-47b3-a386-987cf13ed947

import Mathlib.Analysis.SpecialFunctions.Log.Base
open Real

theorem WorkbookRestored.plus_9408 (x : ℝ) (hx : x > 0 ∧ x ≠ 1) : x^((Real.log 30) / (Real.log x)) = 30   :=  by sorry
