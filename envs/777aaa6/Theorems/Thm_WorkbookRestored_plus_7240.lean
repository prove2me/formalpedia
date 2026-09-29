-- Prove2me | Theorems.Thm_WorkbookRestored_plus_7240
-- name    : WorkbookRestored.plus_7240
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:29:54.199564+00:00
-- url     : https://prove2.me/theorems/25745754-3ae0-4620-99bb-44895d44a225
-- title:
--   Lean-Workbook Plus 7240: Trigonometric identity
-- statement:
--   $\sin{x}\sin{y}=\frac{1}{2}\cdot\left[\cos{\left(x-y\right)}-\cos{\left(x+y\right)}\right]$
--
--   Source: Lean-Workbook row `lean_workbook_plus_7240` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/34f02921-91cb-4ece-8833-422fcad345f7); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_7240; immutable original Prove2Me node 34f02921-91cb-4ece-8833-422fcad345f7

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_7240 : ∀ x y : ℝ, sin x * sin y = 1 / 2 * (cos (x - y) - cos (x + y))   :=  by sorry
