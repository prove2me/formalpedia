-- Prove2me | Theorems.Thm_WorkbookRestored_plus_52
-- name    : WorkbookRestored.plus_52
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:02:54.575395+00:00
-- url     : https://prove2.me/theorems/423685c4-cf8c-4f4e-b91c-35ef1bc386ef
-- title:
--   A cosine square in terms of the doubled angle
-- statement:
--   For every real $x$,
--
--   $$\cos^2(2x)=\frac{1+\cos(4x)}2.$$
--
--   **Formalization Note** This restores source entry `lean_workbook_plus_52` from the Apache-2.0 Lean-Workbook dataset. The mathematical proposition is unchanged; targeted imports and namespace openings supply the constants missing from the original Prove2Me node `8798f16e-9c7c-491b-95bb-6e4e35188d11`. This is a separate corrected node because formal statements and preambles are immutable.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_52; original Prove2Me theorem ID 8798f16e-9c7c-491b-95bb-6e4e35188d11; Apache-2.0.

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real

theorem WorkbookRestored.plus_52 : ∀ x : ℝ, Real.cos (2 * x) ^ 2 = (1 + Real.cos (4 * x)) / 2   :=  by sorry
