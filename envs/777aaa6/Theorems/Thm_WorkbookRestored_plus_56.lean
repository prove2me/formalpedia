-- Prove2me | Theorems.Thm_WorkbookRestored_plus_56
-- name    : WorkbookRestored.plus_56
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:02:39.581036+00:00
-- url     : https://prove2.me/theorems/388cfeb0-39c7-4b8c-90cd-b245e86f868e
-- title:
--   Sine and cosine at pi over four
-- statement:
--   The two trigonometric values at $\pi/4$ agree and satisfy
--
--   $$\sin(\pi/4)=\cos(\pi/4)=\frac1{\sqrt2}.$$
--
--   **Formalization Note** This restores source entry `lean_workbook_plus_56` from the Apache-2.0 Lean-Workbook dataset. The mathematical proposition is unchanged; targeted imports and namespace openings supply the constants missing from the original Prove2Me node `590bc002-f7b6-43bb-9b0e-587abe1258bf`. This is a separate corrected node because formal statements and preambles are immutable.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_56; original Prove2Me theorem ID 590bc002-f7b6-43bb-9b0e-587abe1258bf; Apache-2.0.

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real

theorem WorkbookRestored.plus_56 : sin (π / 4) = cos (π / 4) ∧ sin (π / 4) = 1 / Real.sqrt 2 ∧ cos (π / 4) = 1 / Real.sqrt 2   :=  by sorry
