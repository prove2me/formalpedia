-- Prove2me | Theorems.Thm_lean_workbook_plus_74166
-- name    : lean_workbook_plus_74166
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/c2ec6ad9-1aa4-4e5d-8def-4a1f657ad3f1
-- statement:
--   Given $a, b, c$ positive integers such that $abc=1$, prove that $a=b=c=1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74166 (a b c : ℕ) (h : a * b * c = 1) : a = 1 ∧ b = 1 ∧ c = 1   :=  by sorry
