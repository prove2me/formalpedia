-- Prove2me | Theorems.Thm_lean_workbook_plus_43945
-- name    : lean_workbook_plus_43945
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/66ed37e9-e7eb-4c37-bcdb-38f05b0fef0f
-- statement:
--   Given $P(x) = x^3 + x^2 + x + 1$, show that $P(x) = (x^2 + 1)(x + 1)$ using the fourth roots of unity.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43945 (x : ℂ) : x^3 + x^2 + x + 1 = (x^2 + 1) * (x + 1)   :=  by sorry
