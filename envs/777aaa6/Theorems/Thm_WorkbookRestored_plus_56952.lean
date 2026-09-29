-- Prove2me | Theorems.Thm_WorkbookRestored_plus_56952
-- name    : WorkbookRestored.plus_56952
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:17:23.914909+00:00
-- url     : https://prove2.me/theorems/8de58a65-f6a6-40f7-80f5-debdfd329b86
-- title:
--   Lean-Workbook Plus 56952: Logarithmic inequality
-- statement:
--   For real $x\ge1$, $(\log_2x)(\log_2(x+1))+1\ge1$ and $1>0$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_56952` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/4647264e-3a34-4b43-9222-488c0ecf10dc); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_56952; immutable original Prove2Me node 4647264e-3a34-4b43-9222-488c0ecf10dc

import Mathlib.Analysis.SpecialFunctions.Log.Base
open Real

theorem WorkbookRestored.plus_56952 (x : ℝ) (hx : 1 ≤ x) : Real.logb 2 x * Real.logb 2 (x + 1) + 1 ≥ 1 ∧ 1 > 0   :=  by sorry
