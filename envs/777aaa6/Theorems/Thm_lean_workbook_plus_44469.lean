-- Prove2me | Theorems.Thm_lean_workbook_plus_44469
-- name    : lean_workbook_plus_44469
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/6430b61a-329f-4deb-ab13-bb8c7a3de100
-- statement:
--   For any $ a\not = 2^k - 2009$ we can construct infinetely many $ n$ with $ n|a^n + 2009^n$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44469 (a : ℕ) (ha : a ≠ 2 ^ k - 2009) : ∃ n, n ∣ a ^ n + 2009 ^ n   :=  by sorry
