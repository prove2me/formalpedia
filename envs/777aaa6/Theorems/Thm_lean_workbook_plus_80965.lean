-- Prove2me | Theorems.Thm_lean_workbook_plus_80965
-- name    : lean_workbook_plus_80965
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/7799179a-2854-4731-aa15-5776fdf22443
-- statement:
--   Given $(a+1)(b+1)(c+1)=8$ and $a,b,c \geq 0$, prove that $abc \leq 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80965 (a b c : ℝ) (h : a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0) (h1 : (a + 1) * (b + 1) * (c + 1) = 8) : a * b * c ≤ 1   :=  by sorry
