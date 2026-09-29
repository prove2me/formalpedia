-- Prove2me | Theorems.Thm_WorkbookRestored_plus_78970
-- name    : WorkbookRestored.plus_78970
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:18:06.830838+00:00
-- url     : https://prove2.me/theorems/16edb22b-6e95-49fc-b0f1-126bc1e74099
-- title:
--   Lean-Workbook Plus 78970: Trigonometric identity
-- statement:
--   If $y=\sin(x+\pi/4)$, then $\sin(2x)=2y^2-1$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_78970` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/915e1fc5-b9f9-4a97-b256-f4be27e3c915); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_78970; immutable original Prove2Me node 915e1fc5-b9f9-4a97-b256-f4be27e3c915

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_78970 (x y : ℝ) (h₁ : y = Real.sin (x + Real.pi / 4)) : Real.sin (2 * x) = 2 * y ^ 2 - 1   :=  by sorry
