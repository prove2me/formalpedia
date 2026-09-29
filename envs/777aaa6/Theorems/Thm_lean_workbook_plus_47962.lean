-- Prove2me | Theorems.Thm_lean_workbook_plus_47962
-- name    : lean_workbook_plus_47962
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/acd2c6a9-fa50-4497-98e5-f172ce063673
-- statement:
--   Let $x=\frac{bc}{a^2}$ , $y=\frac{ac}{b^2}$ and $z=\frac{ab}{c^2}$ , where $a$ , $b$ and $c$ are positives. \n Hence, $\left(\sum_{cyc}\frac{1}{\sqrt[3]{1+26x}}\right)^3\sum_{cyc}a^2(a^2+26bc)\geq(a+b+c)^4$ . \n Thus, it remains to prove that $(a+b+c)^4\geq\sum_{cyc}a^2(a^2+26bc)$ , which is obvious.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47962  (x y z a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : x = b * c / a^2)
  (h₂ : y = c * a / b^2)
  (h₃ : z = a * b / c^2) :
  (a + b + c)^4 ≥ a^2 * (a^2 + 26 * b * c) + b^2 * (b^2 + 26 * c * a) + c^2 * (c^2 + 26 * a * b)   :=  by sorry
