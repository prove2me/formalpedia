-- Prove2me | Theorems.Thm_WorkbookRestored_plus_37788
-- name    : WorkbookRestored.plus_37788
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:02:22.748128+00:00
-- url     : https://prove2.me/theorems/c0e167f9-6e9f-4ce9-ad8f-e203a3c1429d
-- title:
--   Lean-Workbook Plus 37788: Trigonometric inequality
-- statement:
--   For $A,B,C\in(0,\pi]$, $9/4+\cos^2A+\cos^2B+\cos^2C\ge\cos A+\cos B+\cos C$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_37788` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/f52d40b2-01b2-4bd3-934c-23ef642552a1); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_37788; immutable original Prove2Me node f52d40b2-01b2-4bd3-934c-23ef642552a1

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_37788 {A B C : ℝ} (hA : 0 < A ∧ A ≤ π ∧ B ≤ π ∧ C ≤ π) (hB : 0 < B ∧ B ≤ π ∧ A ≤ π ∧ C ≤ π) (hC : 0 < C ∧ C ≤ π ∧ A ≤ π ∧ B ≤ π) : 9 / 4 + Real.cos A ^ 2 + Real.cos B ^ 2 + Real.cos C ^ 2 ≥ Real.cos A + Real.cos B + Real.cos C   :=  by sorry
