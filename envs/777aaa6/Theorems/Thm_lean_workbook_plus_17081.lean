-- Prove2me | Theorems.Thm_lean_workbook_plus_17081
-- name    : lean_workbook_plus_17081
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/c66a6ad7-7ba5-49ea-b17c-192ee6e397cc
-- statement:
--   Prove that $a^2+b^2+c^2+d^2=4 \Rightarrow a+b+c+d\le 4$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17081 (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 4) : a + b + c + d ≤ 4   :=  by sorry
