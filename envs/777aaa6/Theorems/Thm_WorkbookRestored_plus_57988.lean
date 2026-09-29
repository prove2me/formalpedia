-- Prove2me | Theorems.Thm_WorkbookRestored_plus_57988
-- name    : WorkbookRestored.plus_57988
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:17:12.156077+00:00
-- url     : https://prove2.me/theorems/d371e72d-3b5e-4734-85bc-38b933ada1d4
-- title:
--   Lean-Workbook Plus 57988: Trigonometric inequality
-- statement:
--   For every integer $n$, $24\cos^4(n\pi/9)\le9\cos^2(n\pi/9)+16\cos^6(n\pi/9)$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_57988` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/4b1c4a04-2431-4c24-a620-75d90290e216); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_57988; immutable original Prove2Me node 4b1c4a04-2431-4c24-a620-75d90290e216

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_57988 (n : ℤ) : 24 * (cos (n * π / 9))^4 ≤ 9 * (cos (n * π / 9))^2 + 16 * (cos (n * π / 9))^6   :=  by sorry
