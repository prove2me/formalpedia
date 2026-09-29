-- Prove2me | Theorems.Thm_lean_workbook_plus_16728
-- name    : lean_workbook_plus_16728
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/07f8d3ac-1aa5-45c7-acae-2871aab45f23
-- statement:
--   Find all functions $f: \mathbb R \to \mathbb R$ such that $ f(x^2-y^2)=(x-y)(f(x)+f(y))$ holds for all real values of $x$ and $y$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16728 (f : ℝ → ℝ): (∀ x y, f (x ^ 2 - y ^ 2) = (x - y) * (f x + f y)) ↔ ∃ a:ℝ, ∀ x, f x = a * x   :=  by sorry
