-- Prove2me | Theorems.Thm_WorkbookRestored_plus_33208
-- name    : WorkbookRestored.plus_33208
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:01:43.728433+00:00
-- url     : https://prove2.me/theorems/d14fc3c7-bb18-4665-b1e3-d4406b53c835
-- title:
--   Lean-Workbook Plus 33208: Trigonometric identity
-- statement:
--   Let $y=\sin x$, $z=\cos x$, $y^2+z^2=1$, and $y^2+3yz-15z^2=0$. Then $9y^2(1-y^2)=(16y^2-15)^2$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_33208` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/a2763798-79f4-485d-a51a-b1ea289c5994); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_33208; immutable original Prove2Me node a2763798-79f4-485d-a51a-b1ea289c5994

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_33208  (x : ℝ)
  (y z : ℝ)
  (h₀ : sin x = y)
  (h₁ : cos x = z)
  (h₂ : y^2 + z^2 = 1)
  (h₃ : y^2 + 3 * y * z - 15 * z^2 = 0) :
  9 * y^2 * (1 - y^2) = (16 * y^2 - 15)^2   :=  by sorry
