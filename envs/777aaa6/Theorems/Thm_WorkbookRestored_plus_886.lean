-- Prove2me | Theorems.Thm_WorkbookRestored_plus_886
-- name    : WorkbookRestored.plus_886
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:02:56.862054+00:00
-- url     : https://prove2.me/theorems/da786565-53ab-429d-8163-4a44de45b0ac
-- title:
--   The sine double-angle identity in half-angle form
-- statement:
--   For every real angle $x$,
--
--   $$\sin x=2\sin(x/2)\cos(x/2).$$
--
--   **Formalization Note** This restores source entry `lean_workbook_plus_886` from the Apache-2.0 Lean-Workbook dataset. The mathematical proposition is unchanged; targeted imports and namespace openings supply the constants missing from the original Prove2Me node `95a4c528-f45b-4594-8358-1aad1c4bb7e4`. This is a separate corrected node because formal statements and preambles are immutable.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_886; original Prove2Me theorem ID 95a4c528-f45b-4594-8358-1aad1c4bb7e4; Apache-2.0.

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real

theorem WorkbookRestored.plus_886 : ∀ x, sin x = 2 * sin (x / 2) * cos (x / 2)   :=  by sorry
