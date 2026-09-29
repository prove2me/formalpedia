-- Prove2me | Theorems.Thm_lean_workbook_plus_80145
-- name    : lean_workbook_plus_80145
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/d3f6f994-3312-4e42-a693-031fe56b609e
-- statement:
--   Let the escalater move at $ A$ stairs in a time unit, person $ A$ move $ 2B$ stairs in that same time unit and person $ Z$ move $ B$ stairs in the time unit. \n\nSo in the case of person $ A$ , the escalator moves $ n-27$ stairs in the same time that person $ A$ moves $ 27$ stairs. Therefore, we can set up the equation that: \n\n $ \frac{n-27}{A}=\frac{27}{2B}$ \n\nSimilarly, for person $ Z$ , the escalator moves $ n-18$ as person $ Z$ moves $ 18$ stairs. Thus: \n\n $ \frac{n-18}{A}=\frac{18}{B}$ \n\nDividing the second by the first gives the following. \n\n $ \frac{n-18}{n-27}=\frac{18}{B} \cdot \frac{2B}{27}= \frac{4}{3}$ \n\nThis gives that, \n\n $ 3(n-18)=4(n-27)$ \n $ n=4\cdot27 - 3\cdot18=54$ \n\nTherefore the answer is $ n=\boxed{54}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80145  (a b z n : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < z ∧ 0 < n)
  (h₁ : 3 * z = 2 * b)
  (h₂ : (n - 27) / a = 27 / (2 * b))
  (h₃ : (n - 18) / a = 18 / b) :
  n = 54   :=  by sorry
