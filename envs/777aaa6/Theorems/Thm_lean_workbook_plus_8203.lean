-- Prove2me | Theorems.Thm_lean_workbook_plus_8203
-- name    : lean_workbook_plus_8203
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/d567a244-bef8-4b7c-81ab-3f57ce00526a
-- statement:
--   Let $P_n=7^n$ (mod10), calculate $\sum_{n=1}^{3981}{P_n}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8203 (P : ℕ → ℕ) (hP: P = fun n => 7 ^ n % 10) : ∑ n in Finset.Icc 1 3981, P n = 19907   :=  by sorry
