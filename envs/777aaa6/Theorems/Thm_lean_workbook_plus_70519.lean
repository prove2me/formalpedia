-- Prove2me | Theorems.Thm_lean_workbook_plus_70519
-- name    : lean_workbook_plus_70519
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/19738ed7-ba44-4274-9c81-fcef5ef09fea
-- statement:
--   We easily check that $1+\frac 1k+\frac 1{k^2}+\frac 1{k^3}<\frac k{k-1}$ $\forall k>1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70519 (k : ℕ) (h : 1 < k) : (1 : ℝ) + 1 / k + (1 / k ^ 2) + 1 / k ^ 3 < k / (k - 1)   :=  by sorry
