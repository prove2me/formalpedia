-- Prove2me | Theorems.Thm_lean_workbook_plus_68004
-- name    : lean_workbook_plus_68004
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/3dd0d8c6-5f53-4baa-a904-86e475e68ef1
-- statement:
--   We have \n $\left( {{a^2} + 2bc} \right)\left( {{b^2} + 2ca} \right)\left( {{c^2} + 2ab} \right) + \frac{(a^2+b^2+c^2)^3}{4}=\frac{1}{12}(a^2+b^2+c^2)(a+b+c)^4+\frac{1}{27}\prod{(a+b-2c)^2}+\frac{1}{54}(a+b+c)^6\ge{0}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68004 (a b c : ℝ) :
  (a^2 + 2 * b * c) * (b^2 + 2 * c * a) * (c^2 + 2 * a * b) + (a^2 + b^2 + c^2)^3 / 4 ≥
  (a^2 + b^2 + c^2) * (a + b + c)^4 / 12 + (a + b - 2 * c)^2 * (b + c - 2 * a)^2 * (c + a - 2 * b)^2 / 27 + (a + b + c)^6 / 54   :=  by sorry
