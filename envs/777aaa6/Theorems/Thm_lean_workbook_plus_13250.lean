-- Prove2me | Theorems.Thm_lean_workbook_plus_13250
-- name    : lean_workbook_plus_13250
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/d985371e-9afe-4898-a7e0-7c6017fd4177
-- statement:
--   Prove the identity $x^{4n}+x^{2n}+1=(x^{2n}+x^n+1)(x^{2n}-x^n+1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13250 (n : ℕ) (x : ℤ) : x ^ (4 * n) + x ^ (2 * n) + 1 = (x ^ (2 * n) + x ^ n + 1) * (x ^ (2 * n) - x ^ n + 1)   :=  by sorry
