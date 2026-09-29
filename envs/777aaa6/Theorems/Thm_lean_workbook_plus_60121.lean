-- Prove2me | Theorems.Thm_lean_workbook_plus_60121
-- name    : lean_workbook_plus_60121
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/62288806-0ef3-4f67-8c84-ee8534f5cad1
-- statement:
--   We claim that $1+3+5+....+(2n+1)-2-4-6-....-2n=n+1.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60121 (n : ℕ) : (∑ i in Finset.range (n+1), (2 * i + 1)) - (∑ i in Finset.range (n+1), 2 * i) = n + 1   :=  by sorry
