-- Prove2me | Theorems.Thm_WorkbookRestored_plus_32152
-- name    : WorkbookRestored.plus_32152
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:01:38.542973+00:00
-- url     : https://prove2.me/theorems/c1ccad04-c5a4-4ef1-a674-cc2426a19bf1
-- title:
--   Lean-Workbook Plus 32152: Trigonometric inequality
-- statement:
--   For $0<x<\pi/2$, $0\le2\sin x\cos x\le1$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_32152` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/c913b54c-0ef6-4b62-a057-db428e6570e8); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_32152; immutable original Prove2Me node c913b54c-0ef6-4b62-a057-db428e6570e8

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_32152 : ∀ x ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ 2 * Real.sin x * Real.cos x ∧ 2 * Real.sin x * Real.cos x ≤ 1   :=  by sorry
