-- Prove2me | Theorems.Thm_lean_workbook_plus_6063
-- name    : lean_workbook_plus_6063
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/abfa9e79-e3f0-4076-8e78-7de4a5a318a5
-- statement:
--   $4T_{n-2}+2T_{n-1}+2T_n=2T_{n-1}+T_{n}+T_{n+1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6063 {n : ℕ} {T : ℕ → ℕ} (h₁ : 4 * T (n - 2) + 2 * T (n - 1) + 2 * T n = 2 * T (n - 1) + T n + T (n + 1)) : 4 * T (n - 2) + 2 * T (n - 1) + 2 * T n = 2 * T (n - 1) + T n + T (n + 1)   :=  by sorry
