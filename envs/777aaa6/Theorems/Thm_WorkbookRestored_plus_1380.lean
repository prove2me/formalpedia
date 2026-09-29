-- Prove2me | Theorems.Thm_WorkbookRestored_plus_1380
-- name    : WorkbookRestored.plus_1380
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:03:04.270407+00:00
-- url     : https://prove2.me/theorems/2226f3c4-b99e-4154-9f71-d07e10db5f02
-- title:
--   Simplifying a sine expression containing 150 degrees
-- statement:
--   The degree-to-radian conversion gives
--
--   $$2\bigl(\sin(150\pi/180)-\sin(80\pi/180)\bigr)=1-2\sin(80\pi/180).$$
--
--   **Formalization Note** This restores source entry `lean_workbook_plus_1380` from the Apache-2.0 Lean-Workbook dataset. The mathematical proposition is unchanged; targeted imports and namespace openings supply the constants missing from the original Prove2Me node `48277d7c-9aeb-489e-9578-2369bb8242c1`. This is a separate corrected node because formal statements and preambles are immutable.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_1380; original Prove2Me theorem ID 48277d7c-9aeb-489e-9578-2369bb8242c1; Apache-2.0.

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real

theorem WorkbookRestored.plus_1380 (x : ℝ) : 2 * (Real.sin (150 * π / 180) - Real.sin (80 * π / 180)) = 1 - 2 * Real.sin (80 * π / 180)   :=  by sorry
