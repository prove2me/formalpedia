-- Prove2me | Theorems.Thm_lean_workbook_plus_7494
-- name    : lean_workbook_plus_7494
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/fcf856b5-cb50-40ed-96f7-7def3568d318
-- statement:
--   Let $a,b $ be reals such that $(a+b) (a+4b) = 9 $ . Prove that $ab\le 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7494 (a b : ℝ) (h : (a + b) * (a + 4 * b) = 9) : a * b ≤ 1   :=  by sorry
