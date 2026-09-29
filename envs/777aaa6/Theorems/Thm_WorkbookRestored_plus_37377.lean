-- Prove2me | Theorems.Thm_WorkbookRestored_plus_37377
-- name    : WorkbookRestored.plus_37377
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:02:14.834907+00:00
-- url     : https://prove2.me/theorems/d1aa5cf9-ede9-422e-9575-cfa08f39c15c
-- title:
--   Lean-Workbook Plus 37377: Exponential inequality
-- statement:
--   For every real $y$, $(e^y+e^{-y})^2\ge(e^y-e^{-y})^2$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_37377` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/68599d79-c105-4ec9-a35f-fdee12b8c8ae); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_37377; immutable original Prove2Me node 68599d79-c105-4ec9-a35f-fdee12b8c8ae

import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real

theorem WorkbookRestored.plus_37377 : ∀ y : ℝ, (exp y + exp (-y)) ^ 2 ≥ (exp y - exp (-y)) ^ 2   :=  by sorry
