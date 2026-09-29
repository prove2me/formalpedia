-- Prove2me | Theorems.Thm_WorkbookRestored_plus_51013
-- name    : WorkbookRestored.plus_51013
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:04:07.307783+00:00
-- url     : https://prove2.me/theorems/d0b2b945-7bf6-4681-b566-5da79b44a614
-- title:
--   Lean-Workbook Plus 51013: Trigonometric inequality
-- statement:
--   For triangle angles $A,B,C>0$ with sum $\pi$, $(\tan(A/2)+\tan(B/2)+\tan(C/2))^2\ge3(\tan(A/2)\tan(B/2)+\tan(B/2)\tan(C/2)+\tan(C/2)\tan(A/2))$. This is the inequality component of the source.
--
--   Source: Lean-Workbook row `lean_workbook_plus_51013` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/9ff5a2ac-e696-48f0-a62a-caf50918ade5); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_51013; immutable original Prove2Me node 9ff5a2ac-e696-48f0-a62a-caf50918ade5

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_51013 :
  ∀ A B C : ℝ, (A + B + C = π ∧ A > 0 ∧ B > 0 ∧ C > 0 → (Real.tan (A / 2) + Real.tan (B / 2) + Real.tan (C / 2))^2 ≥ 3 * (Real.tan (A / 2) * Real.tan (B / 2) + Real.tan (B / 2) * Real.tan (C / 2) + Real.tan (C / 2) * Real.tan (A / 2)))   :=  by sorry
