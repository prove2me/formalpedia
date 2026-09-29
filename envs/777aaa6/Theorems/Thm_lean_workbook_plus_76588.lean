-- Prove2me | Theorems.Thm_lean_workbook_plus_76588
-- name    : lean_workbook_plus_76588
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/55483e2f-763c-4b44-b108-062f3408ebc0
-- statement:
--   Due to the symmetry, we may assume WLOG that $a\ge b \ge c$ . Hence, $a+b \ge c+a \ge b+c$ and $\frac{ab}{a+b} \ge \frac{ca}{c+a} + \frac{bc}{b+c}$ . By Chebychev's inequality, we have $$\left(\sum_{cyc}\frac{ab}{a+b}\right)\left(\sum_{cyc} a+b\right) \le 3\sum_{cyc} ab$$ or $$\sum_{cyc}\frac{ab}{a+b} \le \frac{3(ab+bc+ca)}{2(a+b+c)}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76588  (a b c : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : a ≥ b ∧ b ≥ c) :
  (a * b / (a + b) + b * c / (b + c) + c * a / (c + a)) ≤ (3 * (a * b + b * c + c * a)) / (2 * (a + b + c))   :=  by sorry
