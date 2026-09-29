-- Prove2me | Theorems.Thm_WorkbookRestored_plus_60365
-- name    : WorkbookRestored.plus_60365
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:17:21.083586+00:00
-- url     : https://prove2.me/theorems/9bd951aa-7ade-4d78-992c-e6ee62b6a45b
-- title:
--   Lean-Workbook Plus 60365: Trigonometric identity
-- statement:
--   If $\cos(3x)=-1/2$, then $8\cos^3x-6\cos x+1=0$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_60365` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/6b47a0ca-c8e4-40be-a93d-ca1d3ee56336); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_60365; immutable original Prove2Me node 6b47a0ca-c8e4-40be-a93d-ca1d3ee56336

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_60365 (x : ℝ) (h : Real.cos (3 * x) = -1 / 2) :
  8 * (Real.cos x)^3 - 6 * Real.cos x + 1 = 0   :=  by sorry
