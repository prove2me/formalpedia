-- Prove2me | Theorems.Thm_lean_workbook_plus_9574
-- name    : lean_workbook_plus_9574
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/05488296-f845-42c9-a8f0-00f2e292c091
-- statement:
--   Discuss the convergence of the series based on the behavior of the absolute value of the terms: \\(|\\frac{(-1)^{\\frac{n(n+3)}{2}}}{n}|=\\frac{1}{n}\\)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9574 : ∀ n : ℕ, |(-1 : ℝ)^((n*(n+3))/2)/n| = 1/n   :=  by sorry
