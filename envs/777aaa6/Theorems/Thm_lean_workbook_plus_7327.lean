-- Prove2me | Theorems.Thm_lean_workbook_plus_7327
-- name    : lean_workbook_plus_7327
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/9eefc44c-d4df-4f11-b146-6f6ad21e07d8
-- statement:
--   Prove that \n $ \frac{1}{4} \left( \sum_{k=1}^{n} a_k \right)^2 \left(\sum_{k=1}^{n} b_k \right)^2+\left( \sum_{k=1}^{n} a_kb_k \right)^2 \ge \left( \sum_{k=1}^{n} a_k \right) \left(\sum_{k=1}^{n} b_k \right) \left( \sum_{k=1}^{n} a_kb_k \right). $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7327 (a b : ℕ → ℝ) (n : ℕ) :
  (1 / 4) * (∑ k in Finset.range n, a k) ^ 2 * (∑ k in Finset.range n, b k) ^ 2 +
      (∑ k in Finset.range n, a k * b k) ^ 2 ≥
    (∑ k in Finset.range n, a k) * (∑ k in Finset.range n, b k) * (∑ k in Finset.range n, a k * b k)   :=  by sorry
