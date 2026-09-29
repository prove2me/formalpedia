-- Prove2me | Theorems.Thm_lean_workbook_plus_28207
-- name    : lean_workbook_plus_28207
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/87d74522-7212-4c0d-8c2e-6a0a80ddd7b1
-- statement:
--   Let $1<a_{1}<a_{2}<\cdots$ be a sequence of positive integers. Show that $\frac{2^{a_{1}}}{{a_{1}}!}+\frac{2^{a_{2}}}{{a_{2}}!}+\frac{2^{a_{3}}}{{a_{3}}!}+\cdots$ is irrational.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28207 (a : ℕ → ℕ) (h : ∀ n, 1 < a n) : ¬ ∃ (x : ℚ), ∑' n : ℕ, (2 : ℚ)^(a n) / (a n)! = x   :=  by sorry
