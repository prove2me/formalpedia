-- Prove2me | Theorems.Thm_WorkbookRestored_plus_8018
-- name    : WorkbookRestored.plus_8018
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:29:56.677465+00:00
-- url     : https://prove2.me/theorems/2935500b-dad0-45aa-8b65-c4dfa93c2944
-- title:
--   Lean-Workbook Plus 8018: Logarithmic inequality
-- statement:
--   For every real $x>0$, $\log x/(x+1)\le\log(x+1)/x$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_8018` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/28c86209-6dbe-40b5-9e1a-04af070184a6); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_8018; immutable original Prove2Me node 28c86209-6dbe-40b5-9e1a-04af070184a6

import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real

theorem WorkbookRestored.plus_8018 (x : ℝ) (hx : 0 < x) : (Real.log x) / (x + 1) ≤ (Real.log (x + 1)) / x   :=  by sorry
