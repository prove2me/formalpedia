-- Prove2me | Theorems.Thm_WorkbookRestored_plus_1571
-- name    : WorkbookRestored.plus_1571
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:03:02.593706+00:00
-- url     : https://prove2.me/theorems/ab681509-a044-48c7-b21d-393eaf3df3f3
-- title:
--   A uniform bound for a sine-cosine linear combination
-- statement:
--   For all real $a,b,x$,
--
--   $$|a\sin x+b\cos x|\le\sqrt{a^2+b^2}.$$
--
--   This node records the inequality component of the source exercise.
--
--   **Formalization Note** This restores source entry `lean_workbook_plus_1571` from the Apache-2.0 Lean-Workbook dataset. The mathematical proposition is unchanged; targeted imports and namespace openings supply the constants missing from the original Prove2Me node `0f5b5d9e-9779-4f70-bcbc-cdf84dafbe84`. This is a separate corrected node because formal statements and preambles are immutable.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_1571; original Prove2Me theorem ID 0f5b5d9e-9779-4f70-bcbc-cdf84dafbe84; Apache-2.0.

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real

theorem WorkbookRestored.plus_1571 (a b x : ℝ) : |a * sin x + b * cos x| ≤ Real.sqrt (a ^ 2 + b ^ 2)   :=  by sorry
