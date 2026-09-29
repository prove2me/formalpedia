-- Prove2me | Theorems.Thm_lean_workbook_plus_73541
-- name    : lean_workbook_plus_73541
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/0c12c22b-7658-451c-b19e-1bde0d1b3b96
-- statement:
--   Let the distance from Jennifer's house to the point where she turned around be $a$ , and the distance from the point where she turned around be $b$ . WLOG assume she walks at $2$ mph, thus bicycling at $5$ mph. She takes $a+b$ hours just walking to the store and back, and $a+\frac{2a+2b}{5}$ going back home and going to the store on her bike. Thus we require $a+\frac{2a+2b}{5} \leq a+b \implies 2a \leq 3b \implies \frac{b}{a} \geq \frac{2}{3} \implies \frac{b+a}{a} \geq \frac{5}{3} \implies \frac{a}{a+b} \leq \frac{3}{5}=60\%$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73541  (a b : ℝ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : a + b > 0)
  (h₂ : 2 * a ≤ 3 * b) :
  a / (a + b) ≤ 3 / 5   :=  by sorry
