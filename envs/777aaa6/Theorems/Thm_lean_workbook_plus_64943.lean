-- Prove2me | Theorems.Thm_lean_workbook_plus_64943
-- name    : lean_workbook_plus_64943
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/5907685a-1d85-4c6a-a978-168da82ef5b0
-- statement:
--   In August, they bought $\frac{3125}{1.25}=2500$ liters of fuel. In October, they bought $\frac{3080}{1.25}=2464$ liters of fuel. We have $2464=2500\cdot (1+x)\cdot (1-x)$ which leads to $2464=2500\cdot (1-x^2)$ . We have $\frac{621}{625}=1-x^2$ . $x^2=\frac{9}{625}$ . $x=\frac{3}{25}$ . $2500\cdot \frac{28}{25}=2800$ $2800\cdot 1.25=\boxed{3500}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64943  (x : ℝ)
  (h₀ : x^2 = 9 / 625) :
  (2500 * (1 + x) * (1 - x) : ℝ) = 2464   :=  by sorry
