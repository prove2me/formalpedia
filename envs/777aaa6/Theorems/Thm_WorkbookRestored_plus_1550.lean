-- Prove2me | Theorems.Thm_WorkbookRestored_plus_1550
-- name    : WorkbookRestored.plus_1550
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:03:03.76464+00:00
-- url     : https://prove2.me/theorems/03d48f37-f720-4c19-984c-9d3b8387f356
-- title:
--   Strict positivity of a quadratic trigonometric expression
-- statement:
--   For every real $x$,
--
--   $$x^2\sin x+x\cos x+x^2+\frac12>0.$$
--
--   **Formalization Note** This restores source entry `lean_workbook_plus_1550` from the Apache-2.0 Lean-Workbook dataset. The mathematical proposition is unchanged; targeted imports and namespace openings supply the constants missing from the original Prove2Me node `9b495279-2056-4c8d-a03d-15d810b6abcc`. This is a separate corrected node because formal statements and preambles are immutable.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_1550; original Prove2Me theorem ID 9b495279-2056-4c8d-a03d-15d810b6abcc; Apache-2.0.

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real

theorem WorkbookRestored.plus_1550 (x : ℝ) :  x ^ 2 * Real.sin x + x * Real.cos x + x ^ 2 + 1 / 2 > 0   :=  by sorry
