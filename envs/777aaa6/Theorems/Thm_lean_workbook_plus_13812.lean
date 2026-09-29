-- Prove2me | Theorems.Thm_lean_workbook_plus_13812
-- name    : lean_workbook_plus_13812
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/b6109220-8a34-415d-a701-73968762404a
-- statement:
--   Find $ax^5+by^5$ if the real numbers $a$ , $b$ , $x$ , and $y$ satisfy the equations \n\n \begin{eqnarray*} ax + by &=& 3, \ ax^2 + by^2 &=& 7, \ ax^3 + by^3 &=& 16, \ ax^4 + by^4 &=& 42. \end{eqnarray*}
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13812 (a b x y : ℝ) (h₁ : a * x + b * y = 3) (h₂ : a * x^2 + b * y^2 = 7) (h₃ : a * x^3 + b * y^3 = 16) (h₄ : a * x^4 + b * y^4 = 42) : a * x^5 + b * y^5 = 20   :=  by sorry
