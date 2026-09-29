-- Prove2me | Theorems.Thm_WorkbookRestored_plus_20175
-- name    : WorkbookRestored.plus_20175
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:31:25.207629+00:00
-- url     : https://prove2.me/theorems/77b02090-e2a8-4eef-b1aa-c4476cef262b
-- title:
--   Lean-Workbook Plus 20175: Trigonometric inequality
-- statement:
--   If $0\le x\le1$ and $y=\arcsin x$, then $\cos y=\sqrt{1-x^2}$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_20175` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/d330103a-4c72-4b0c-be8a-b888591eeafc); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_20175; immutable original Prove2Me node d330103a-4c72-4b0c-be8a-b888591eeafc

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
open Real

theorem WorkbookRestored.plus_20175 (x y : ℝ) (h₁ : 0 ≤ x ∧ x ≤ 1) (h₂ : y = arcsin x) : cos y = Real.sqrt (1 - x^2)   :=  by sorry
