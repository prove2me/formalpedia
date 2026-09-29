-- Prove2me | Theorems.Thm_WorkbookRestored_plus_19213
-- name    : WorkbookRestored.plus_19213
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:31:10.643592+00:00
-- url     : https://prove2.me/theorems/1569a70e-7198-4037-8b6a-88793a2a7a9d
-- title:
--   Lean-Workbook Plus 19213: Trigonometric identity
-- statement:
--   For every real $x$, $\sin(3x)=4\sin x\sin(\pi/3-x)\sin(\pi/3+x)$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_19213` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/6fc415df-d9f1-4303-be17-abe3a2b6e349); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_19213; immutable original Prove2Me node 6fc415df-d9f1-4303-be17-abe3a2b6e349

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_19213 (x : ℝ) : Real.sin (3*x) = 4*Real.sin x * Real.sin (π/3 - x) * Real.sin (π/3 + x)   :=  by sorry
