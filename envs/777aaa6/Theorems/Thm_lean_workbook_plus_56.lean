-- Prove2me | Theorems.Thm_lean_workbook_plus_56
-- name    : lean_workbook_plus_56
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/590bc002-f7b6-43bb-9b0e-587abe1258bf
-- statement:
--   Prove that $\sin \frac{\pi}{4}=\cos \frac{\pi}{4}=\frac{1}{\sqrt{2}}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56 : sin (π / 4) = cos (π / 4) ∧ sin (π / 4) = 1 / Real.sqrt 2 ∧ cos (π / 4) = 1 / Real.sqrt 2   :=  by sorry
