-- Prove2me | Theorems.Thm_WorkbookRestored_plus_41599
-- name    : WorkbookRestored.plus_41599
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:02:33.48299+00:00
-- url     : https://prove2.me/theorems/c5f59045-b4b7-45c3-a982-a2779d6020d7
-- title:
--   Lean-Workbook Plus 41599: Exponential inequality
-- statement:
--   For $0\le x\le1$, $(e^x-1)/(e^x-x)\ge0$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_41599` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/d8eb57c7-b79e-43c5-93b4-663749aa5e23); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_41599; immutable original Prove2Me node d8eb57c7-b79e-43c5-93b4-663749aa5e23

import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real

theorem WorkbookRestored.plus_41599 (x : ℝ) (hx: 0 ≤ x ∧ x ≤ 1) : (exp x - 1) / (exp x - x) ≥ 0   :=  by sorry
