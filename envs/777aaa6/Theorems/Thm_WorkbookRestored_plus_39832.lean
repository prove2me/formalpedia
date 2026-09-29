-- Prove2me | Theorems.Thm_WorkbookRestored_plus_39832
-- name    : WorkbookRestored.plus_39832
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:02:21.150362+00:00
-- url     : https://prove2.me/theorems/509549e1-c8ba-41ab-8847-0eb23f547d0a
-- title:
--   Lean-Workbook Plus 39832: Trigonometric identity
-- statement:
--   For every real $x$, $\sin^2x\cos^2x=\sin^2(2x)/4$ and $\sin^2x=(1-\cos(2x))/2$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_39832` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/3cba94be-322e-4785-a730-0027fe068f09); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_39832; immutable original Prove2Me node 3cba94be-322e-4785-a730-0027fe068f09

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_39832 : ∀ x : ℝ, ((sin x)^2 * (cos x)^2) = (sin (2 * x))^2 / 4 ∧ (sin x)^2 = (1 - cos (2 * x)) / 2   :=  by sorry
