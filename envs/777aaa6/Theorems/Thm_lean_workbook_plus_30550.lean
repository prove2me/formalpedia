-- Prove2me | Theorems.Thm_lean_workbook_plus_30550
-- name    : lean_workbook_plus_30550
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/58fed514-b80c-4444-aa72-fad92f08e1d7
-- statement:
--   For any integer $n\ge2$ , we have \n\n $$\displaystyle\prod_{k=2}^n\left(1-\frac{1}{k^2}\right)=\prod_{k=2}^n\left(\frac{k-1}{k}\cdot\frac{k+1}{k}\right)=\left(\prod_{k=2}^n\frac{k-1}{k}\right)\cdot\left(\prod_{k=2}^n\frac{k+1}{k}\right)=\frac{1}{n}\cdot\frac{n+1}{2}=\frac{n+1}{2n}.$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30550 : ∀ n ≥ 2, (∏ k in (Finset.Icc 2 n), (1 - 1 / k ^ 2)) = (n + 1) / (2 * n)   :=  by sorry
