-- Prove2me | Theorems.Thm_lean_workbook_plus_80328
-- name    : lean_workbook_plus_80328
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/a410ecbf-1d2b-43b7-ab33-0d56dc1ff468
-- statement:
--   Let $a,b,c$ be positive real numbers such that $ a^2+b^2+c^2=1.$ Prove that \n\n $$2ab+2bc+7ca\leq 4$$ $$3ab+3bc+7ca\leq \frac{9}{2}$$ $$2ab+2bc+3ca\leq \frac{3+\sqrt{41}}{4}$$ $$2ab+2bc+5ca\leq \frac{5+\sqrt{57}}{4}$$ $$3ab+3bc+8ca\leq \frac{4+\sqrt{34}}{2}$$ $$ab+2bc+3ca\leq \frac{\sqrt{42}}{3}cos\left(\frac{1}{3}\arccos \frac {9\sqrt{42}}{98}\right)$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80328 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) :
  2 * a * b + 2 * b * c + 7 * c * a ≤ 4 ∧ 3 * a * b + 3 * b * c + 7 * c * a ≤ 9 / 2 ∧
  2 * a * b + 2 * b * c + 3 * c * a ≤ (3 + Real.sqrt 41) / 4 ∧
  2 * a * b + 2 * b * c + 5 * c * a ≤ (5 + Real.sqrt 57) / 4 ∧
  3 * a * b + 3 * b * c + 8 * c * a ≤ (4 + Real.sqrt 34) / 2 ∧
  a * b + 2 * b * c + 3 * c * a ≤ Real.sqrt 42 / 3 * Real.cos (Real.arccos 9 * Real.sqrt 42 / 98)   :=  by sorry
