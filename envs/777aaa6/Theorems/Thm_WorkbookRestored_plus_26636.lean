-- Prove2me | Theorems.Thm_WorkbookRestored_plus_26636
-- name    : WorkbookRestored.plus_26636
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:00:50.753895+00:00
-- url     : https://prove2.me/theorems/e521c718-f391-4de1-ac42-dc211e031ab5
-- title:
--   Lean-Workbook Plus 26636: Logarithmic inequality
-- statement:
--   For every real $x>0$, $\log x\le x-1$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_26636` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/38baa84e-75d4-4a60-b30c-b9808a31e71e); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_26636; immutable original Prove2Me node 38baa84e-75d4-4a60-b30c-b9808a31e71e

import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real

theorem WorkbookRestored.plus_26636 (x : ℝ) (hx : 0 < x) : Real.log x ≤ x - 1   :=  by sorry
