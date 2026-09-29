-- Prove2me | Theorems.Thm_WorkbookRestored_plus_79397
-- name    : WorkbookRestored.plus_79397
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:18:07.628459+00:00
-- url     : https://prove2.me/theorems/e256e1a0-5af4-46ed-8bac-ef2613960b86
-- title:
--   Lean-Workbook Plus 79397: Logarithmic inequality
-- statement:
--   For $0<x<y$, $2^x+\log x/\log2<2^y+\log y/\log2$, with real exponentiation.
--
--   Source: Lean-Workbook row `lean_workbook_plus_79397` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/92faa752-736c-430f-97f9-eea0ca3fb813); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_79397; immutable original Prove2Me node 92faa752-736c-430f-97f9-eea0ca3fb813

import Mathlib.Analysis.SpecialFunctions.Log.Base
open Real

theorem WorkbookRestored.plus_79397 (x y : ℝ) (hxy : x < y) (hx : 0 < x) (hy : 0 < y) : (2:ℝ)^x + (Real.log x) / (Real.log 2) < (2:ℝ)^y + (Real.log y) / (Real.log 2)   :=  by sorry
