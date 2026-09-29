-- Prove2me | Theorems.Thm_lean_workbook_plus_8058
-- name    : lean_workbook_plus_8058
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/bfb2d1bd-7b54-48b8-926b-635e84e56cbd
-- statement:
--   Let $a\geq 4,b,c\geq 0,a+b\leq 2c,x,y,z\in R$. Prove that $(a-3)(b-x^2-y^2-z^2)\leq (c-x-y-z)^2.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8058 (a b c x y z : ℝ) (ha : a ≥ 4) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a + b ≤ 2 * c) : (a - 3) * (b - x ^ 2 - y ^ 2 - z ^ 2) ≤ (c - x - y - z) ^ 2   :=  by sorry
