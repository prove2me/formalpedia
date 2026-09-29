-- Prove2me | Theorems.Thm_lean_workbook_plus_42995
-- name    : lean_workbook_plus_42995
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/077f614c-545b-4628-90ac-1a97773997b3
-- statement:
--   Prove that $c\left(n,k\right)=c\left(n,n-k\right)$ for all $n\geq k\geq 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42995 (n k : ℕ) (h₁ : n ≥ k) (h₂ : k ≥ 0) : choose n k = choose n (n-k)   :=  by sorry
