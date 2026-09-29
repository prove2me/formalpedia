-- Prove2me | Theorems.Thm_WorkbookRestored_plus_2048
-- name    : WorkbookRestored.plus_2048
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:03:10.217241+00:00
-- url     : https://prove2.me/theorems/e85f367a-11eb-457b-bf0b-489066523410
-- title:
--   Subtracting two from a real exponent
-- statement:
--   With $r=\log_2 5$,
--
--   $$2^{r-2}=\frac{2^r}{2^2}.$$
--
--   **Formalization Note** This restores source entry `lean_workbook_plus_2048` from the Apache-2.0 Lean-Workbook dataset. The mathematical proposition is unchanged; targeted imports and namespace openings supply the constants missing from the original Prove2Me node `708b5936-4988-4b07-bd45-2ec77a455817`. This is a separate corrected node because formal statements and preambles are immutable.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_2048; original Prove2Me theorem ID 708b5936-4988-4b07-bd45-2ec77a455817; Apache-2.0.

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
open Real

theorem WorkbookRestored.plus_2048 : (2:ℝ)^(Real.logb 2 5 - 2) = (2:ℝ)^(Real.logb 2 5) / (2:ℝ)^2   :=  by sorry
