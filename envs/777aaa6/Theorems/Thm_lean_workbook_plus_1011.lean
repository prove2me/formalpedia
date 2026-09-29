-- Prove2me | Theorems.Thm_lean_workbook_plus_1011
-- name    : lean_workbook_plus_1011
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/aa9c32b0-8ad0-413c-8224-e8f6df6bd925
-- statement:
--   Let $f(x)=\sum_{k=0}^{\infty}a_{k}x^{k}$ be a power series ( $a_{k}\in \mathbb{R}$ ). Suppose that $f(x)$ converges at $c$ where $c>0$ . Show that $f(x)$ converges at any $x$ with $|x|<c$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1011 (a : ℕ → ℝ) (c x : ℝ) (hc : 0 < c) (hx : |x| < c) : ∃ y : ℝ, y = ∑' k : ℕ, a k * x ^ k   :=  by sorry
