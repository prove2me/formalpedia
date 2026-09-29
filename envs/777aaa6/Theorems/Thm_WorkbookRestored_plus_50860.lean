-- Prove2me | Theorems.Thm_WorkbookRestored_plus_50860
-- name    : WorkbookRestored.plus_50860
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:04:03.151998+00:00
-- url     : https://prove2.me/theorems/20b99ee7-007e-49e1-b6de-ab61b896781d
-- title:
--   Lean-Workbook Plus 50860: Trigonometric identity
-- statement:
--   For real $x$ and integer $k$, $\cos x=\pi/2+\sin x+2\pi k$ if and only if $\cos(x+\pi/4)=(4k+1)\pi/(2\sqrt2)$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_50860` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/ae08a050-b812-4c10-bd5c-e545ecb1ceb0); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_50860; immutable original Prove2Me node ae08a050-b812-4c10-bd5c-e545ecb1ceb0

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_50860 (x : ℝ) (k : ℤ) : (Real.cos x = Real.pi / 2 + Real.sin x + 2 * Real.pi * k) ↔ (Real.cos (x + Real.pi / 4) = (2 * Real.sqrt 2)⁻¹ * (4 * k + 1) * Real.pi)   :=  by sorry
