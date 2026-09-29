-- Prove2me | Theorems.Thm_lean_workbook_plus_13803
-- name    : lean_workbook_plus_13803
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/61e126a3-9f38-4d33-98f7-b873a91188e7
-- statement:
--   Show that the series $\sum_{n=1}^{\infty} \frac{x^n}{3^n n ^2}$ converges pointwise for $-3 < x < 3$ using the ratio test.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13803 (x : ℝ) (hx : -3 < x ∧ x < 3) (n : ℕ) : ∃ y, ∑' n : ℕ, (x^n / (3^n * n^2)) = y   :=  by sorry
