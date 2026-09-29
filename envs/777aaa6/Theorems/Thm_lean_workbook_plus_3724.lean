-- Prove2me | Theorems.Thm_lean_workbook_plus_3724
-- name    : lean_workbook_plus_3724
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/a68c1af7-067a-42dc-ac51-1e4a8173c8ea
-- statement:
--   Let $x$ be a positive real number, prove the following inequality.\n\n$(1+x)^n\geq 1+nx\ (n=1,\ 2,\ \cdots).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3724 : ∀ n : ℕ, (1 + x)^n ≥ 1 + n*x   :=  by sorry
