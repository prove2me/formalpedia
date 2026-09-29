-- Prove2me | Theorems.Thm_lean_workbook_plus_69410
-- name    : lean_workbook_plus_69410
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/f77043b1-a807-4e4a-81e8-96c531d5b321
-- statement:
--   And so $a_n=\left(2^{2^{1-n}}-1\right)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69410 (n : ℕ) : ∃ a : ℕ, a = (2^(2^(1-n))-1)^2   :=  by sorry
