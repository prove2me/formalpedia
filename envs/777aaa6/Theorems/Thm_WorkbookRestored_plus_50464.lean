-- Prove2me | Theorems.Thm_WorkbookRestored_plus_50464
-- name    : WorkbookRestored.plus_50464
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:03:55.425332+00:00
-- url     : https://prove2.me/theorems/6ed0a8ec-f5f6-439b-8da5-c157664d6a16
-- title:
--   Lean-Workbook Plus 50464: Logarithmic inequality
-- statement:
--   $1<\log3/\log2<2$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_50464` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/b1b1e0e2-701a-4092-a59c-7d472f23d764); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_50464; immutable original Prove2Me node b1b1e0e2-701a-4092-a59c-7d472f23d764

import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real

theorem WorkbookRestored.plus_50464 : 1 < Real.log 3 / Real.log 2 ∧ Real.log 3 / Real.log 2 < 2   :=  by sorry
