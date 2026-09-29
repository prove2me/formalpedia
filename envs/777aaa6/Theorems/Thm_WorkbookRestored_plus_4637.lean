-- Prove2me | Theorems.Thm_WorkbookRestored_plus_4637
-- name    : WorkbookRestored.plus_4637
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:29:27.871287+00:00
-- url     : https://prove2.me/theorems/df62fdc5-b444-4c21-add8-f98aa4606ea4
-- title:
--   Lean-Workbook Plus 4637: Trigonometric identity
-- statement:
--   The expression $-\tfrac12(\cos 1-\cos 0)$ equals $(1-\cos 1)/2$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_4637` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/2f6b15f4-7075-42d4-a752-a73db775e2c3); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_4637; immutable original Prove2Me node 2f6b15f4-7075-42d4-a752-a73db775e2c3

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_4637 :
  -(1 / 2) * (Real.cos 1 - Real.cos 0) = (1 - Real.cos 1) / 2   :=  by sorry
