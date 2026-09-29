-- Prove2me | Theorems.Thm_WorkbookRestored_plus_60454
-- name    : WorkbookRestored.plus_60454
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:17:20.874747+00:00
-- url     : https://prove2.me/theorems/a2403b86-aa0b-4283-abc8-3278075f83db
-- title:
--   Lean-Workbook Plus 60454: Trigonometric identity
-- statement:
--   Let real $t=\tan(x/2)$. Then $10t/(1+t^2)-3(1-t^2)/(1+t^2)-3=0$ if and only if $t=3/5$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_60454` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/3c45f94b-5e90-4887-add4-d646f04617a4); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_60454; immutable original Prove2Me node 3c45f94b-5e90-4887-add4-d646f04617a4

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_60454 (t : ℝ) (x : ℝ) (h₁ : t = Real.tan (x / 2)) : (10 * t / (1 + t^2) - 3 * (1 - t^2) / (1 + t^2) - 3 = 0) ↔ t = 3 / 5   :=  by sorry
