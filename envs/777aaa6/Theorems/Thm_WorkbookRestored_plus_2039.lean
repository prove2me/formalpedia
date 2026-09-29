-- Prove2me | Theorems.Thm_WorkbookRestored_plus_2039
-- name    : WorkbookRestored.plus_2039
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:03:16.822306+00:00
-- url     : https://prove2.me/theorems/82f34155-1acf-4abb-a344-ee58c2621dae
-- title:
--   A numerical instance of the sine subtraction identity
-- statement:
--   For the real sine and cosine functions,
--
--   $$\sin30\cos10-\sin10\cos30=\sin20.$$
--
--   **Formalization Note** This restores source entry `lean_workbook_plus_2039` from the Apache-2.0 Lean-Workbook dataset. The mathematical proposition is unchanged; targeted imports and namespace openings supply the constants missing from the original Prove2Me node `fa5c7b4b-18c4-4181-9392-dbd4ddfaa9bc`. This is a separate corrected node because formal statements and preambles are immutable.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_2039; original Prove2Me theorem ID fa5c7b4b-18c4-4181-9392-dbd4ddfaa9bc; Apache-2.0.

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real

theorem WorkbookRestored.plus_2039 : sin 30 * cos 10 - sin 10 * cos 30 = sin 20   :=  by sorry
