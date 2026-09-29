-- Prove2me | Theorems.Thm_WorkbookRestored_plus_1885
-- name    : WorkbookRestored.plus_1885
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:03:09.336071+00:00
-- url     : https://prove2.me/theorems/3ebf8b83-e0b0-45e9-bb38-4e48e0e6b461
-- title:
--   The triangle double-angle sine identity
-- statement:
--   Let $A,B,C$ be real angles with $A+B+C=\pi$. Under the source bounds $0<A\le\pi$, $B\le\pi$, and $C\le\pi$,
--
--   $$\sin(2A)+\sin(2B)+\sin(2C)=4\sin A\sin B\sin C.$$
--
--   **Formalization Note** This restores source entry `lean_workbook_plus_1885` from the Apache-2.0 Lean-Workbook dataset. The mathematical proposition is unchanged; targeted imports and namespace openings supply the constants missing from the original Prove2Me node `3953b176-0356-450f-ae73-974abaaf1ae8`. This is a separate corrected node because formal statements and preambles are immutable.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_1885; original Prove2Me theorem ID 3953b176-0356-450f-ae73-974abaaf1ae8; Apache-2.0.

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real

theorem WorkbookRestored.plus_1885 (A B C : ℝ) (hA : 0 < A ∧ A <= π ∧ B <= π ∧ C <= π ∧ A + B + C = π) : Real.sin (2 * A) + Real.sin (2 * B) + Real.sin (2 * C) = 4 * Real.sin A * Real.sin B * Real.sin C   :=  by sorry
