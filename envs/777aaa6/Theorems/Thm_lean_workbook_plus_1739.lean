-- Prove2me | Theorems.Thm_lean_workbook_plus_1739
-- name    : lean_workbook_plus_1739
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/ae41b8c7-a9d2-49e0-86b8-a946bfe0238e
-- statement:
--   Let $a_k = \frac{k}{108}$ , evaluate $\sum_{k=1}^{108}\frac{a_k^2}{1-2a_k+2a_k^2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1739 (a : ℕ → ℚ) (h : ∀ k, a k = k / 108) : ∑ k in Finset.Icc 1 108, (a k ^ 2 / (1 - 2 * a k + 2 * a k ^ 2)) = 18   :=  by sorry
