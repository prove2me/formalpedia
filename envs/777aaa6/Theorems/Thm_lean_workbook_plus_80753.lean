-- Prove2me | Theorems.Thm_lean_workbook_plus_80753
-- name    : lean_workbook_plus_80753
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/e053357c-403c-4bda-8994-7d5e50452bb2
-- statement:
--   Let $a,b$ be real numbers such that $a+b\geq 2$ \nProve that $a^4+b^4 \geq a^3+b^3.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80753 (a b : ℝ) (h : a + b ≥ 2) : a^4 + b^4 ≥ a^3 + b^3   :=  by sorry
