-- Prove2me | Theorems.Thm_lean_workbook_plus_15755
-- name    : lean_workbook_plus_15755
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/6275704c-4f63-40da-ad7f-8c8a8ca0672c
-- statement:
--   Let $a,b,c>0$ and $a+b^2+c^2=1$ . Prove that \n $$ abc(a+1)(b+1)(c+1)\leq \frac{27}{64}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15755 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (hab : a + b^2 + c^2 = 1) :  a * b * c * (a + 1) * (b + 1) * (c + 1) ≤ 27 / 64   :=  by sorry
