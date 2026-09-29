-- Prove2me | Theorems.Thm_lean_workbook_plus_72668
-- name    : lean_workbook_plus_72668
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/1c7b5a94-c4de-4c1f-946d-e881fe2a93f4
-- statement:
--   Let $a,b $ be reals such that $(2a+b) (2b+a) = 9$ . Prove that $ab\le 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72668 (a b : ℝ) (h : (2 * a + b) * (2 * b + a) = 9) : a * b ≤ 1   :=  by sorry
