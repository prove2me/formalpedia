-- Prove2me | Theorems.Thm_lean_workbook_plus_5035
-- name    : lean_workbook_plus_5035
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/9559b169-21d2-40ea-9a2e-38e0bcddbb13
-- statement:
--   Prove the identity $_nC_k = $_nC_(n-k)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5035 (n k : ℕ) (h₁ : k ≤ n) : choose n k = choose n (n - k)   :=  by sorry
