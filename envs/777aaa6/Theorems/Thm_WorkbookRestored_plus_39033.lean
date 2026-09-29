-- Prove2me | Theorems.Thm_WorkbookRestored_plus_39033
-- name    : WorkbookRestored.plus_39033
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:02:19.951979+00:00
-- url     : https://prove2.me/theorems/0b731d91-9b44-4e09-abf1-c5f928221fe5
-- title:
--   Lean-Workbook Plus 39033: Trigonometric identity
-- statement:
--   For real $x$ and integer $k$, $\cos x=\pi/2-\sin x+2\pi k$ if and only if $\sin(x+\pi/4)=(4k+1)\pi/(2\sqrt2)$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_39033` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/c702ea8f-f511-4d79-a825-b0aeb40cb865); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_39033; immutable original Prove2Me node c702ea8f-f511-4d79-a825-b0aeb40cb865

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_39033  (x : ℝ) (k : ℤ) :
  (Real.cos x = Real.pi / 2 - Real.sin x + 2 * Real.pi * k) ↔
  (Real.sin (x + Real.pi / 4) = (4 * k + 1) * Real.pi / (2 * Real.sqrt 2))   :=  by sorry
