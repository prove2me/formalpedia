-- Prove2me | Theorems.Thm_WorkbookRestored_plus_11374
-- name    : WorkbookRestored.plus_11374
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:30:14.539204+00:00
-- url     : https://prove2.me/theorems/c3c67eea-e1c1-49d3-8c18-6b33ebf27b68
-- title:
--   Lean-Workbook Plus 11374: Trigonometric identity
-- statement:
--   For every real $x$, $\cos x=1-2\sin^2(x/2)$.
--
--   Source: Lean-Workbook row `lean_workbook_plus_11374` (Apache-2.0). The unchanged proposition comes from [the original record](https://prove2.me/theorems/2781408f-6beb-46b5-bb30-9fb59020fe4b); its missing mathematical imports and namespaces are restored here.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_11374; immutable original Prove2Me node 2781408f-6beb-46b5-bb30-9fb59020fe4b

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
open Real

theorem WorkbookRestored.plus_11374 : ∀ x : ℝ, Real.cos x = 1 - 2 * (Real.sin (x / 2))^2   :=  by sorry
