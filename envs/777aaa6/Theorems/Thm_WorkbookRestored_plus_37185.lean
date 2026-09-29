-- Prove2me | Theorems.Thm_WorkbookRestored_plus_37185
-- name    : WorkbookRestored.plus_37185
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:02:13.337146+00:00
-- url     : https://prove2.me/theorems/3daf7438-cf3e-4ccc-83cf-3f66a6a72860
-- title:
--   Lean-Workbook Plus 37185: Trigonometric identity
-- statement:
--   For every real $x$, $\sin^2x+\sin^2(2x)+\sin^2(3x)+\cos^2x+\cos^2(2x)+\cos^2(3x)=3$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_37185` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/59330872-4cd8-4b47-8f66-d2f966b841da); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_37185; immutable original Prove2Me node 59330872-4cd8-4b47-8f66-d2f966b841da

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_37185 : ∀ x : ℝ, (Real.sin x)^2 + (Real.sin (2 * x))^2 + (Real.sin (3 * x))^2 + (Real.cos x)^2 + (Real.cos (2 * x))^2 + (Real.cos (3 * x))^2 = 3   :=  by sorry
