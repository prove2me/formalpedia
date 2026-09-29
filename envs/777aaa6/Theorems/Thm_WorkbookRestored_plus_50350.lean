-- Prove2me | Theorems.Thm_WorkbookRestored_plus_50350
-- name    : WorkbookRestored.plus_50350
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:03:47.868556+00:00
-- url     : https://prove2.me/theorems/c9a0e001-890f-4aff-bcb4-e87bdfb8c469
-- title:
--   Lean-Workbook Plus 50350: Logarithmic inequality
-- statement:
--   For real $x>1$, $\log\bigl(x(x^2+3)/(3x^2+1)\bigr)<x$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_50350` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/5fcc9b70-0f5b-4f1c-8f80-f9f495bda15d); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_50350; immutable original Prove2Me node 5fcc9b70-0f5b-4f1c-8f80-f9f495bda15d

import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real

theorem WorkbookRestored.plus_50350 (x : ℝ) (hx : 1 < x) : Real.log (x * (x ^ 2 + 3) / (3 * x ^ 2 + 1)) < x   :=  by sorry
