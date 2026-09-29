-- Prove2me | Theorems.Thm_lean_workbook_plus_25404
-- name    : lean_workbook_plus_25404
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/a3f80463-c821-4e8f-ab1c-8907550641de
-- statement:
--   If we let $f(x)=\sum_{k=1}^n \binom{n-1}{k-1} x^{k-1}=(1+x)^{n-1},$ then \n $ \int_{0}^{2} f(x) dx=(\sum_{k=1}^{n-1}\binom{n-1}{k-1}\frac{x^k}{k}) |_{0}^{2}=\sum_{k=1}^{n-1}\binom{n-1}{k-1}\frac{2^k}{k}, $ so \n $ \sum_{k=1}^n\frac{2^{k-1}}{k}\binom{n-1}{k-1}=\frac{1}{2}\int_{0}^{2} f(x) dx=\frac{1}{2} \int_{0}^{2} (1+x)^{n-1}dx=\frac{3^n-1}{2n}. $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25404 : ∀ n : ℕ, n > 0 → ∑ k in Finset.range n, (2 : ℝ)^(k-1) / k * (n-1).choose (k-1) = (3^n - 1) / (2 * n)   :=  by sorry
