-- Prove2me | Theorems.Thm_WorkbookRestored_plus_57418
-- name    : WorkbookRestored.plus_57418
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:17:10.85883+00:00
-- url     : https://prove2.me/theorems/de262f0a-b5e9-4fc4-b4bd-32ef1bf77e8d
-- title:
--   Lean-Workbook Plus 57418: Trigonometric inequality
-- statement:
--   For a natural number $n$ with $0<n<9$, $\cos(n\pi/9)+\cos((9-n)\pi/9)=0$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_57418` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/b6851f55-3b3d-4258-b320-cb80cfc12628); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_57418; immutable original Prove2Me node b6851f55-3b3d-4258-b320-cb80cfc12628

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_57418 (n : ℕ) (hn : 0 < n ∧ n < 9) : Real.cos (n * π / 9) + Real.cos ((9 - n) * π / 9) = 0   :=  by sorry
