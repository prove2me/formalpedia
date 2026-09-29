-- Prove2me | Theorems.Thm_lean_workbook_plus_24730
-- name    : lean_workbook_plus_24730
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/cf258ed4-0301-45a0-8fc0-b05c4d8b6352
-- statement:
--   Let $x$ = $a+b$ $y$ = $b+c$ $z$ = $a+c$ \n\n $\frac{1}{2}$ ( $\frac{x+z-y}{y}$ + $\frac{x+y-z}{z}$ + $\frac{y+z-x}{x}$ = $\frac{1}{2}$ ( $\frac{x}{y}$ + $\frac{y}{x}$ + $\frac{x}{z}$ + $\frac{z}{x}$ + $\frac{y}{z}$ + $\frac{x}{y}$ - $3$ ) $>=$ $\frac{1}{2}$ ( $2+2+2-3)$ = $\frac{3}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24730  (x y z : ℝ)
  (h₀ : x = a + b)
  (h₁ : y = b + c)
  (h₂ : z = a + c)
  (h₃ : 0 < x ∧ 0 < y ∧ 0 < z) :
  1 / 2 * ((x + z - y) / y + (x + y - z) / z + (y + z - x) / x) ≥ 3 / 2   :=  by sorry
