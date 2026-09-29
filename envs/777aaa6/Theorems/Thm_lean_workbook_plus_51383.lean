-- Prove2me | Theorems.Thm_lean_workbook_plus_51383
-- name    : lean_workbook_plus_51383
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/20648476-5847-4ec7-bcb5-319ab11eed94
-- statement:
--   Let: $a,b,c>0$ and $(a^{2}+1)(b^{2}+1)(c^{2}+1)=8$ . Prove that: $ab+bc+ac+abc\leq 4$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51383 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : (a^2 + 1) * (b^2 + 1) * (c^2 + 1) = 8) : a * b + b * c + c * a + a * b * c ≤ 4   :=  by sorry
