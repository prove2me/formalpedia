-- Prove2me | Theorems.Thm_WorkbookRestored_plus_15898
-- name    : WorkbookRestored.plus_15898
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:30:45.324988+00:00
-- url     : https://prove2.me/theorems/4bba611b-16f6-472a-a8d7-010910d2063d
-- title:
--   Lean-Workbook Plus 15898: Trigonometric inequality
-- statement:
--   For every real $\alpha$, $-1\le\cos\alpha\le1$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_15898` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/61e7434b-f3cd-4a04-8453-1dfd8d79737b); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_15898; immutable original Prove2Me node 61e7434b-f3cd-4a04-8453-1dfd8d79737b

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_15898 (α : ℝ) : -1 ≤ Real.cos α ∧ Real.cos α ≤ 1   :=  by sorry
