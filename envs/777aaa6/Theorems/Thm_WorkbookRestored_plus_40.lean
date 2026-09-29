-- Prove2me | Theorems.Thm_WorkbookRestored_plus_40
-- name    : WorkbookRestored.plus_40
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T11:02:43.700995+00:00
-- url     : https://prove2.me/theorems/1b305777-c0fb-40a9-98ae-7da964596ca7
-- title:
--   Cosine exceeds sine before pi over four
-- statement:
--   For every real angle $0<\theta<\pi/4$,
--
--   $$\cos\theta>\sin\theta.$$
--
--   **Formalization Note** This restores source entry `lean_workbook_plus_40` from the Apache-2.0 Lean-Workbook dataset. The mathematical proposition is unchanged; targeted imports and namespace openings supply the constants missing from the original Prove2Me node `ddeae32b-26bb-4b03-9b22-6afd34b69fdd`. This is a separate corrected node because formal statements and preambles are immutable.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, row lean_workbook_plus_40; original Prove2Me theorem ID ddeae32b-26bb-4b03-9b22-6afd34b69fdd; Apache-2.0.

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
open Real

theorem WorkbookRestored.plus_40 :
  ∀ θ : ℝ, 0 < θ ∧ θ < Real.pi / 4 → Real.cos θ > Real.sin θ   :=  by sorry
