-- Prove2me | Theorems.Thm_WorkbookRestored_plus_70928
-- name    : WorkbookRestored.plus_70928
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:17:46.541584+00:00
-- url     : https://prove2.me/theorems/86cd3915-e4ca-4bae-8d2d-5a0d07c87999
-- title:
--   Lean-Workbook Plus 70928: Exponential inequality
-- statement:
--   For $x\geq 0$ it is true that $e^{-x} \leq 1$ .
--
--   Source: Lean-Workbook row `lean_workbook_plus_70928` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/0c9a05c4-f910-4188-b8aa-890da08e7ad8); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_70928; immutable original Prove2Me node 0c9a05c4-f910-4188-b8aa-890da08e7ad8

import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real

theorem WorkbookRestored.plus_70928 : ∀ x ≥ 0, exp (-x) ≤ 1   :=  by sorry
