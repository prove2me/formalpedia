-- Prove2me | Theorems.Thm_WorkbookRestored_plus_162
-- name    : WorkbookRestored.plus_162
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:03:08.426247+00:00
-- url     : https://prove2.me/theorems/d0dd310e-1500-42b7-9eff-0e7c9352a0b6
-- title:
--   A shifted-angle sine and cosine identity
-- statement:
--   For all real $a,b,c$,
--
--   $$\cos(a+b)\sin b-\cos(a+c)\sin c=\sin(a+b)\cos b-\sin(a+c)\cos c.$$
--
--   **Formalization Note** This restores source entry `lean_workbook_plus_162` from the Apache-2.0 Lean-Workbook dataset. The mathematical proposition is unchanged; targeted imports and namespace openings supply the constants missing from the original Prove2Me node `4517984b-eb73-4f67-a1df-a9ab9509f558`. This is a separate corrected node because formal statements and preambles are immutable.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_162; original Prove2Me theorem ID 4517984b-eb73-4f67-a1df-a9ab9509f558; Apache-2.0.

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real

theorem WorkbookRestored.plus_162  (a b c : ℝ) :
  Real.cos (a + b) * Real.sin b - Real.cos (a + c) * Real.sin c
    = Real.sin (a + b) * Real.cos b - Real.sin (a + c) * Real.cos c   :=  by sorry
