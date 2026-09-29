-- Prove2me | Theorems.Thm_lean_workbook_plus_52281
-- name    : lean_workbook_plus_52281
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/831f5ad2-c307-42eb-97ff-24b77cfc11d5
-- statement:
--   Let y=1 : $ h(x+1)=h(x)+1 $ $ \to h(x+n)= h(x) +n $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52281 (x n : ℕ) (h : ℕ → ℕ) (h₁ : ∀ x, h (x + 1) = h x + 1) : h (x + n) = h x + n   :=  by sorry
