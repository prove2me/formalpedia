-- Prove2me | Theorems.Thm_lean_workbook_plus_79362
-- name    : lean_workbook_plus_79362
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/7aa627de-8119-425e-b117-34d6095eaed3
-- statement:
--   Suppose that for some $j \geq 2k$ , we have $f(x + i) = x + k + i$ for all $0 \leq i < j$ . Consider that $x + j - k \leq f(x + j) \leq x + j + k$ . But all values between $x + j - k = f(x + j - 2k)$ and $x + j + k - 1 = f(x + j - 1)$ have been taken. So, $f(x + j) = x + j + k$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79362  (x k : ℕ)
  (f : ℕ → ℕ)
  (h₀ : 0 < k)
  (h₁ : ∀ i, 0 ≤ i ∧ i < 2 * k → f (x + i) = x + k + i)
  (h₂ : 2 * k ≤ j)
  (h₃ : ∀ i, 0 ≤ i ∧ i < j → x + j - k ≤ f (x + i) ∧ f (x + i) ≤ x + j + k)
  (h₄ : ∀ i, 0 ≤ i ∧ i < j → ∀ j', x + j - k ≤ j' ∧ j' ≤ x + j + k → j' = f (x + i)) :
  ∀ i, 0 ≤ i ∧ i < j → f (x + i) = x + i + k   :=  by sorry
