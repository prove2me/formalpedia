-- Prove2me | Theorems.Thm_WorkbookRestored_plus_11366
-- name    : WorkbookRestored.plus_11366
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:30:22.509516+00:00
-- url     : https://prove2.me/theorems/0690a2da-2fa5-4313-82d2-cd967f651bdb
-- title:
--   Lean-Workbook Plus 11366: Trigonometric inequality
-- statement:
--   Prove that $\sin x+\cos x\leq\sqrt 2$ , where $\ x\in\left(0,\frac{\pi}{2}\right)$ .
--
--   Source: Lean-Workbook row `lean_workbook_plus_11366` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/90ef2907-1f6d-4068-94b1-1102b9072d53); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_11366; immutable original Prove2Me node 90ef2907-1f6d-4068-94b1-1102b9072d53

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_11366 (x : ℝ) (hx : 0 < x ∧ x < Real.pi / 2) :
  Real.sin x + Real.cos x ≤ Real.sqrt 2   :=  by sorry
