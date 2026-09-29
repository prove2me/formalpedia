-- Prove2me | Theorems.Thm_WorkbookRestored_plus_78674
-- name    : WorkbookRestored.plus_78674
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:18:05.352604+00:00
-- url     : https://prove2.me/theorems/e8d36e27-b4ac-4c35-ad94-db6af63e0f54
-- title:
--   Lean-Workbook Plus 78674: Trigonometric identity
-- statement:
--   $\sin{x}-\sin{y}=2\cos{\frac{x+y}{2}}\sin{\frac{x-y}{2}}$
--
--   Source: Lean-Workbook row `lean_workbook_plus_78674` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/f69493b0-c76c-4358-baca-b7ca2ee37df3); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_78674; immutable original Prove2Me node f69493b0-c76c-4358-baca-b7ca2ee37df3

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_78674 (x y : ℝ) : sin x - sin y = 2 * cos ((x + y) / 2) * sin ((x - y) / 2)   :=  by sorry
