-- Prove2me | Theorems.Thm_lean_workbook_plus_36457
-- name    : lean_workbook_plus_36457
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/6e118b61-d6a9-43dc-b6f4-34163341d783
-- statement:
--   Prove that $\forall n \ge k \ge 0 \in \mathbb{N},\text{ we have } c(n,k)=c(n,n-k)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36457 (n k : ℕ) (h₁ : n ≥ k) (h₂ : 0 ≤ k) : choose n k = choose n (n - k)   :=  by sorry
