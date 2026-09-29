-- Prove2me | Theorems.Thm_WorkbookRestored_plus_77082
-- name    : WorkbookRestored.plus_77082
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:18:03.479314+00:00
-- url     : https://prove2.me/theorems/e9cd4ec8-fa7b-443b-857e-3639504ac21b
-- title:
--   Lean-Workbook Plus 77082: Trigonometric identity
-- statement:
--   For real $x$ with $\cos x\ne0$, $\sin(2x)/\cos x=2\sin x$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_77082` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/e4761a13-d769-4158-bbff-bb3af5a32a4e); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_77082; immutable original Prove2Me node e4761a13-d769-4158-bbff-bb3af5a32a4e

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_77082  (x : ℝ)
  (h₀ : cos x ≠ 0) :
  sin (2 * x) / cos x = 2 * sin x   :=  by sorry
