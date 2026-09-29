-- Prove2me | Theorems.Thm_lean_workbook_plus_14309
-- name    : lean_workbook_plus_14309
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/3ac3b173-c265-4f25-8837-440fb334dda6
-- statement:
--   If $a$ and $b$ are poitive integers and if $a> b+1$ , prove that $(a+b)^{2} > 4ab+3$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14309 (a b : ℕ) (h₁ : a > b + 1) (h₂ : b > 0) : (a + b) ^ 2 > 4 * a * b + 3   :=  by sorry
