-- Prove2me | Theorems.Thm_lean_workbook_plus_57305
-- name    : lean_workbook_plus_57305
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/73a44f56-65f4-4773-b0fd-529c3c26f65d
-- statement:
--   Let $a_i$ and $b_j$ be positives such that $a_i < b_j$ for any naturals $i$ and $j$. Prove that:\n\n$$\sqrt{\frac{1}{3n}\sum_{k=1}^n(a_k^2+a_kb_k+b_k^2)}\geq\sqrt[3]{\frac{1}{2n}\sum_{k=1}^n(a_k+b_k)a_kb_k}.$$\n\nBeautiful problem.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57305 (n : ℕ) (a b : ℕ → ℝ) (hab : ∀ i j, a i < b j) : (1 / (3 * n) * ∑ k in Finset.range n, (a k ^ 2 + a k * b k + b k ^ 2))^(1 / 2) ≥ (1 / (2 * n) * ∑ k in Finset.range n, (a k + b k) * a k * b k)^(1 / 3)   :=  by sorry
