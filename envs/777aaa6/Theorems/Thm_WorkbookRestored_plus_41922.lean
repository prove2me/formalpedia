-- Prove2me | Theorems.Thm_WorkbookRestored_plus_41922
-- name    : WorkbookRestored.plus_41922
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:02:32.653287+00:00
-- url     : https://prove2.me/theorems/40474632-67c9-4435-985f-3b5e440da0f1
-- title:
--   Lean-Workbook Plus 41922: Trigonometric inequality
-- statement:
--   For every real $x$, $\cos^3x-\cos^2x=\cos^2x(\cos x-1)\le0$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_41922` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/1d232657-78c6-4098-8bbb-18805f970767); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_41922; immutable original Prove2Me node 1d232657-78c6-4098-8bbb-18805f970767

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_41922 : ∀ x : ℝ, (cos x)^3 - (cos x)^2 = (cos x)^2 * (cos x - 1) ∧ (cos x)^2 * (cos x - 1) ≤ 0   :=  by sorry
