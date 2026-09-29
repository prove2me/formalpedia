-- Prove2me | Theorems.Thm_lean_workbook_plus_42563
-- name    : lean_workbook_plus_42563
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/8d0bd9e1-caa2-4d34-905e-6c46834f81c8
-- statement:
--   SolutionUsing $1-\frac{1}{1+x} \le \log(1+x) \le x$ for all $x>-1$ we have \n $$\frac{1}{2}=\sum _{k=1}^n \frac{k}{n^2+n}\le \sum _{k=1}^n \frac{k}{n^2+k}=\sum _{k=1}^n \left(1-\frac{1}{1+\frac{k}{n^2}}\right)\le \sum _{k=1}^n \log \left(1+\frac{k}{n^2}\right)\le \sum _{k=1}^n \frac{k}{n^2}=\frac{n+1}{2 n}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42563 (n : ℕ) : 1 / 2 ≤ ∑ k in Finset.Icc 1 n, (k / (n ^ 2 + k)) ∧ ∑ k in Finset.Icc 1 n, (k / (n ^ 2 + k)) ≤ (n + 1) / (2 * n)   :=  by sorry
