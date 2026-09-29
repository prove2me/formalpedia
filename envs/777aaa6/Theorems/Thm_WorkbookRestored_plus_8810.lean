-- Prove2me | Theorems.Thm_WorkbookRestored_plus_8810
-- name    : WorkbookRestored.plus_8810
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:30:05.966001+00:00
-- url     : https://prove2.me/theorems/0716f42b-db45-4d08-9272-a80c10fc75e3
-- title:
--   Lean-Workbook Plus 8810: Trigonometric inequality
-- statement:
--   Prove that $\sqrt{x\cos x} \le \frac{x + \cos x}{2}$ for $x\in [0,\frac{\pi}{2}]$ using the Arithmetic Mean-Geometric Mean (AM-GM) inequality.
--
--   Source: Lean-Workbook row `lean_workbook_plus_8810` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/4cb6ee1f-83cc-4be2-b63b-16815b307fda); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_8810; immutable original Prove2Me node 4cb6ee1f-83cc-4be2-b63b-16815b307fda

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_8810 (x : ℝ) (hx : 0 ≤ x ∧ x ≤ π/2) :
  Real.sqrt (x * Real.cos x) ≤ (x + Real.cos x) / 2   :=  by sorry
