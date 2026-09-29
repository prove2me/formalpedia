-- Prove2me | Theorems.Thm_WorkbookRestored_plus_20139
-- name    : WorkbookRestored.plus_20139
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:31:14.559267+00:00
-- url     : https://prove2.me/theorems/1c14fd88-b844-464b-b8e3-ffb742312b6c
-- title:
--   Lean-Workbook Plus 20139: Logarithmic inequality
-- statement:
--   For positive real $x,y$, $\log x+\log y=\log(xy)$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_20139` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/bd9117b0-cfcf-47e4-8899-59eeae1c9a32); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_20139; immutable original Prove2Me node bd9117b0-cfcf-47e4-8899-59eeae1c9a32

import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real

theorem WorkbookRestored.plus_20139 : ∀ x y : ℝ, x > 0 ∧ y > 0 → Real.log x + Real.log y = Real.log (x*y)   :=  by sorry
