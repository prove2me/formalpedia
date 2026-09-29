-- Prove2me | Theorems.Thm_lean_workbook_plus_58675
-- name    : lean_workbook_plus_58675
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/38d50cd1-bfa8-45d4-b44b-60f173e1cd73
-- statement:
--   Note that $\log 2^{k}=k\log 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58675 : ∀ k : ℕ, Real.log (2^k) = k * Real.log 2   :=  by sorry
