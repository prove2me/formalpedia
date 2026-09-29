-- Prove2me | Theorems.Thm_lean_workbook_plus_72427
-- name    : lean_workbook_plus_72427
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/413e3891-cb99-4a64-b070-65e440549dfb
-- statement:
--   Suppose we have the following recurrence\n\n\(2a_n = \sum_{k=0}^n\binom{n}{k}a_k\) where \(a_0=1\) \n\nShow that the power series \(\mathcal{A}(z) = \sum_{n=0}^{\infty}\frac{a_nz^n}{n!}\) satisfies the recurrence\n\n\(\mathcal{A}(z)e^z = 2\mathcal{A}(z) - 1\) \n
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72427 (a : ℕ → ℝ) (A : ℝ → ℝ) (hA : A = fun z ↦ ∑' n : ℕ, (a n * z ^ n / n!)) (ha : a 0 = 1) (ha' : ∀ n, 2 * a n = ∑ k in Finset.range (n + 1), (n.choose k) * a k) : A z * exp z = 2 * A z - 1   :=  by sorry
