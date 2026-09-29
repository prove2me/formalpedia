-- Prove2me | Theorems.Thm_WorkbookRestored_plus_22764
-- name    : WorkbookRestored.plus_22764
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:31:26.824769+00:00
-- url     : https://prove2.me/theorems/fc536b30-6151-4915-a7a5-cbefb6fc83fe
-- title:
--   Lean-Workbook Plus 22764: Exponential inequality
-- statement:
--   Prove that $e^{-x} > -\frac{2x}{x^2 + 1}$ for $x \in \mathbb{R}^-$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_22764` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/1ec70b39-528f-4017-b5a5-97f0810c5f3b); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_22764; immutable original Prove2Me node 1ec70b39-528f-4017-b5a5-97f0810c5f3b

import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real

theorem WorkbookRestored.plus_22764 (x : ℝ) (hx : x < 0) :
  Real.exp (-x) > -2 * x / (x ^ 2 + 1)   :=  by sorry
