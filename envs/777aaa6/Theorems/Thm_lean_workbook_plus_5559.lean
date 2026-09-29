-- Prove2me | Theorems.Thm_lean_workbook_plus_5559
-- name    : lean_workbook_plus_5559
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/4f4893a1-56c4-455a-91f4-4016b74fc284
-- statement:
--   Identity for $ a,b,c$ (even if $ a+b+c\ne1$ ): $ {10 \left( {a}^{3}+{b}^{3}+{c}^{3} \right) \left( a+b+c \right) ^{2} -9\left({a}^{5}+{b}^{5}+{c}^{5}\right)= \left( a+b+c \right) ^{5}+\frac{15}{2} \left( a+b \right) \left( a+c \right) \left( b+c \right) \left( \left( a-b \right) ^{2}+ \left( a-c \right) ^{2}+ \left( b-c \right) ^{2} \right)}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5559 (a b c : ℝ) :
  10 * (a^3 + b^3 + c^3) * (a + b + c)^2 - 9 * (a^5 + b^5 + c^5) =
    (a + b + c)^5 + (15 / 2) * (a + b) * (a + c) * (b + c) * ((a - b)^2 + (a - c)^2 + (b - c)^2)   :=  by sorry
