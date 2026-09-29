-- Prove2me | Theorems.Thm_WorkbookRestored_plus_61757
-- name    : WorkbookRestored.plus_61757
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:17:30.266781+00:00
-- url     : https://prove2.me/theorems/d397f9b6-1b42-4d62-bc37-e9df86fd3ad6
-- title:
--   Lean-Workbook Plus 61757: Exponential inequality
-- statement:
--   For $-1<x<0$, $e^x<1<1/(1+x)$; for $x>0$, $e^x>1>1/(1+x)$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_61757` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/4c08e189-022b-4c66-8aa6-54b181129d98); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_61757; immutable original Prove2Me node 4c08e189-022b-4c66-8aa6-54b181129d98

import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real

theorem WorkbookRestored.plus_61757 : ∀ x ∈ Set.Ioo (-1 : ℝ) 0, exp x < 1 ∧ 1 < 1 / (1 + x) ∧ ∀ x ∈ Set.Ioi 0, exp x > 1 ∧ 1 > 1 / (1 + x)   :=  by sorry
