-- Prove2me | Theorems.Thm_lean_workbook_plus_60354
-- name    : lean_workbook_plus_60354
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/725040b8-d024-48fc-88f8-550ee245a61a
-- statement:
--   Prove that $f(x)^2 = x^4$ implies $f(x) = x^2$ for all $x \in \mathbb{R}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60354 ∀ f : ℝ → ℝ, (∀ x, f x ^ 2 = x ^ 4) → ∀ x, f x = x ^ 2   :=  by sorry
