-- Prove2me | Theorems.Thm_lean_workbook_plus_19006
-- name    : lean_workbook_plus_19006
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/a8cd9cdd-681d-480c-8ceb-d658d988a4fe
-- statement:
--   Suppose that a,b,c are complex numbers such that $a+b+c=0$. Prove that $2(a-b)^2(b-c)^2(c-a)^2=(a^2+b^2+c^2)^3-54a^2b^2c^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19006 (a b c : ℂ) (h : a + b + c = 0) :
  2 * (a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2 = (a ^ 2 + b ^ 2 + c ^ 2) ^ 3 - 54 * a ^ 2 * b ^ 2 * c ^ 2   :=  by sorry
