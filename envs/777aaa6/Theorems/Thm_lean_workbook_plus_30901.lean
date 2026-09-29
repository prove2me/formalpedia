-- Prove2me | Theorems.Thm_lean_workbook_plus_30901
-- name    : lean_workbook_plus_30901
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/6d4d2abd-06d0-440e-8a71-5a7601fd565d
-- statement:
--   ${k+2}=2\frac{a+b+c}{a}\to \frac{2}{k+2}=\frac{a}{a+b+c}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30901 (a b c k : ℝ) : k + 2 = 2 * (a + b + c) / a → 2 / (k + 2) = a / (a + b + c)   :=  by sorry
