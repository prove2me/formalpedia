-- Prove2me | Theorems.Thm_lean_workbook_plus_15301
-- name    : lean_workbook_plus_15301
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/f77ff772-60ec-4876-ae94-8e998852689a
-- statement:
--   Prove the following inequality.\n\n$\frac{n-1}{2n+2}<\left(\frac{1}{n}\right)^n+\left(\frac{2}{n}\right)^n+\cdots\cdots+\left(\frac{n-1}{n}\right)^n<\frac{n}{n+1}\ \ (n=2,3,\cdots)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15301 (n : ℕ) : (n - 1) / (2 * n + 2) < (∑ k in Finset.Icc 1 (n - 1), (k / n)^n) ∧ (∑ k in Finset.Icc 1 (n - 1), (k / n)^n) < n / (n + 1)   :=  by sorry
