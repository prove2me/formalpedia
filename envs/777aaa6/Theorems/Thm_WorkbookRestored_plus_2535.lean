-- Prove2me | Theorems.Thm_WorkbookRestored_plus_2535
-- name    : WorkbookRestored.plus_2535
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:27:43.750607+00:00
-- url     : https://prove2.me/theorems/3ca2101b-d821-48fe-9b9a-58e84f6405a3
-- title:
--   Lean-Workbook Plus 2535: Trigonometric identity
-- statement:
--   Prove the following identity. $\cos{2x} = 2\cos^2x - 1$
--
--   Source: Lean-Workbook row `lean_workbook_plus_2535` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/c9dfc668-632f-4671-88d4-5b62d89f49ef); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_2535; immutable original Prove2Me node c9dfc668-632f-4671-88d4-5b62d89f49ef

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_2535 : ∀ x : ℝ, Real.cos (2 * x) = 2 * (Real.cos x)^2 - 1   :=  by sorry
