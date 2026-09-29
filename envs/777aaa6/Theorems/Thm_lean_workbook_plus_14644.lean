-- Prove2me | Theorems.Thm_lean_workbook_plus_14644
-- name    : lean_workbook_plus_14644
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/57ae1d7d-bb40-4f7a-9a13-74fee4a83d6c
-- statement:
--   Let $a,b,c$ be real numbers such that $a+b+c=1$ and $a^3+b^3+c^3=25$ . Find the value of $(a-1)(b-1)(c-1)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14644 (a b c : ℝ) (h₁ : a + b + c = 1) (h₂ : a^3 + b^3 + c^3 = 25) : (a - 1) * (b - 1) * (c - 1) = 8   :=  by sorry
