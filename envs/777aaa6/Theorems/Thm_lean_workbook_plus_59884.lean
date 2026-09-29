-- Prove2me | Theorems.Thm_lean_workbook_plus_59884
-- name    : lean_workbook_plus_59884
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/eca840f7-f064-4d6d-a934-9cf461fcf7f9
-- statement:
--   Given the identity $a^2 + b^2 = (a + b)^2 - 2ab$ and $a^3 + b^3 = (a + b)(a^2 - ab + b^2)$, prove that $\sin^6{x} + \cos^6{x} - 1 = -3\sin^2{x}\cos^2{x}$ using these identities.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59884 : ∀ x : ℝ, sin x ^ 6 + cos x ^ 6 - 1 = -3 * sin x ^ 2 * cos x ^ 2   :=  by sorry
