-- Prove2me | Theorems.Thm_lean_workbook_plus_18891
-- name    : lean_workbook_plus_18891
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/9e0f8acc-c22b-404e-b5ca-0f533963e79e
-- statement:
--   Let $ 3^{k}\;\leq \; 2n+1 \;<\; 3^{k+1}\;$ . Prove that every positive odd integer $ m \;\neq\; 3^{k}$ and $ 3\;\leq \;m \;\leq\;2n+1$ has a power of $ 3$ strictly smaller than $ k\;$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18891 (n k : ℕ) (h₁ : 3^k ≤ 2 * n + 1) (h₂ : 2 * n + 1 < 3^(k + 1)) (m : ℕ) (h₃ : 3 ≤ m) (h₄ : m ≤ 2 * n + 1) (h₅ : m ≠ 3^k) : ∃ x : ℕ, 3^x < m   :=  by sorry
