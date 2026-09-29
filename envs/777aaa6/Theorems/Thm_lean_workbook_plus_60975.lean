-- Prove2me | Theorems.Thm_lean_workbook_plus_60975
-- name    : lean_workbook_plus_60975
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/da8f0a44-c69e-4d36-bf9a-3a64fd1c2ab3
-- statement:
--   if n is odd, then set $a = (3n^2 - 1)/2 , b = n^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60975 (n : ℤ) (h : n % 2 = 1) : ∃ a b : ℤ, a = (3 * n ^ 2 - 1) / 2 ∧ b = n ^ 2   :=  by sorry
