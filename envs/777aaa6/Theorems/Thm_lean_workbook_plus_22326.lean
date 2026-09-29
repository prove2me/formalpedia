-- Prove2me | Theorems.Thm_lean_workbook_plus_22326
-- name    : lean_workbook_plus_22326
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/6356bde0-880e-4da9-b378-c2437898a534
-- statement:
--   Apply Cauchy-schwarz inequality on $\left(\frac{x}{\sqrt{a}},\sqrt{a}\right)$ and similarly, $y,b$ instead of $x,a$ \n $\left(\frac{x^2}{a}+\frac{y^2}{b}\right)(a+b)\geq (x+y)^2\implies \frac{x^2}{a}+\frac{y^2}{b}\geq\frac{(x+y)^2}{a+b}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22326 {x y : ℝ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : (x ^ 2 / a + y ^ 2 / b) * (a + b) ≥ (x + y) ^ 2   :=  by sorry
