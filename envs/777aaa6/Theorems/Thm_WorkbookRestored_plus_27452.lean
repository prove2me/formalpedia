-- Prove2me | Theorems.Thm_WorkbookRestored_plus_27452
-- name    : WorkbookRestored.plus_27452
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:00:59.473998+00:00
-- url     : https://prove2.me/theorems/c6289878-bb34-4183-97d7-1d0ca5ad8546
-- title:
--   Lean-Workbook Plus 27452: Trigonometric identity
-- statement:
--   For every real $x$, $\sin(3x)=(1+2\cos(2x))\sin x$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_27452` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/eec86142-595b-451f-8c59-d05295f91289); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_27452; immutable original Prove2Me node eec86142-595b-451f-8c59-d05295f91289

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_27452 (x : ℝ) : Real.sin (3*x) = (1 + 2*Real.cos (2*x))*Real.sin x   :=  by sorry
