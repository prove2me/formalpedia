-- Prove2me | Theorems.Thm_lean_workbook_plus_43008
-- name    : lean_workbook_plus_43008
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/a4b6317c-8853-4157-9055-9c6c36de29f8
-- statement:
--   Hence or otherwise show that $\frac{(5a)! (5b)!}{( a! b! (3a+b)! (a+3b)! )}$ is integral for any positive integers a, b.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43008 (a b : ℕ) : ∃ k : ℕ, (5 * a)! * (5 * b)! / (a! * b! * (3 * a + b)! * (a + 3 * b)!) = k   :=  by sorry
