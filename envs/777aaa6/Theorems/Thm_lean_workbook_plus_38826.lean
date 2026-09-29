-- Prove2me | Theorems.Thm_lean_workbook_plus_38826
-- name    : lean_workbook_plus_38826
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/b1f91ed0-9d0a-424a-9283-7f4a94c15dcc
-- statement:
--   Let $b_0=k,b_1={{k+\epsilon}\over 2}$ and $b_{i+1}={{b_i+\epsilon}\over 2}$ . This is the sequence of upper bounds. The proof is with induction, if $|a_{i+N}|\le b_i$ then $|a_{i+N+1}|\le {{|a_{i+N}|+\epsilon}\over 2}\le {{b_i+\epsilon}\over 2}$ , which is $b_{i+1}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38826  (k ε : ℝ)
  (a : ℕ → ℝ)
  (b : ℕ → ℝ)
  (h₀ : 0 < k ∧ 0 < ε)
  (h₁ : ∀ n, b 0 = k ∧ b (n + 1) = (b n + ε) / 2)
  (h₂ : ∀ n, |a (n + N)| ≤ b n) :
  ∀ n, |a (n + N + 1)| ≤ b (n + 1)   :=  by sorry
