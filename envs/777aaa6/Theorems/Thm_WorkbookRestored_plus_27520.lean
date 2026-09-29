-- Prove2me | Theorems.Thm_WorkbookRestored_plus_27520
-- name    : WorkbookRestored.plus_27520
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:01:05.525975+00:00
-- url     : https://prove2.me/theorems/975f64f7-aa43-4a7d-a8e6-e74f4e8d8f4f
-- title:
--   Lean-Workbook Plus 27520: Trigonometric identity
-- statement:
--   For every real $x$, $\cos(3x)-\cos(5x)=2\sin x\sin(4x)$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_27520` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/718537aa-1d88-48ee-95fc-2a415706697c); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_27520; immutable original Prove2Me node 718537aa-1d88-48ee-95fc-2a415706697c

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_27520 (x : ℝ) :
  Real.cos (3 * x) - Real.cos (5 * x) = 2 * Real.sin x * Real.sin (4 * x)   :=  by sorry
