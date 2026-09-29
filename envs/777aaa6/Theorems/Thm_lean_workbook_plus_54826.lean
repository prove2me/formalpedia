-- Prove2me | Theorems.Thm_lean_workbook_plus_54826
-- name    : lean_workbook_plus_54826
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/658c2810-4355-4d79-bcbb-a3c34f8bb283
-- statement:
--   $ 0=a+b+c+d\implies d=-a-b-c$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54826 (a b c d : ℝ) (h : a + b + c + d = 0) : d = -a - b - c   :=  by sorry
