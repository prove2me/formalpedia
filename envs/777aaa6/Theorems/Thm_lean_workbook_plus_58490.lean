-- Prove2me | Theorems.Thm_lean_workbook_plus_58490
-- name    : lean_workbook_plus_58490
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/cd572d36-9477-4637-8ca5-9af7c7115293
-- statement:
--   $|a+bi|$ means distance from origin. By distance formula, this is obviously $\sqrt{a^2+b^2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58490 : ∀ a b : ℝ, Complex.abs (a + b * Complex.I) = Real.sqrt (a ^ 2 + b ^ 2)   :=  by sorry
