-- Prove2me | Theorems.Thm_lean_workbook_plus_56485
-- name    : lean_workbook_plus_56485
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/93cf3e4e-79f1-4e00-9adc-209d0874f765
-- statement:
--   This inequality is equivalent to $\sum \frac{a+b+c}{2a+b+c}\ge \frac{9}{4}$ . By CS we have \n $(a+b+c) (\sum \frac{1}{2a+b+c})\ge(a+b+c) (\frac{9}{4(a+b+c)})=\frac{9}{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56485 : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → (a + b + c) * (1 / (2 * a + b + c) + 1 / (2 * b + a + c) + 1 / (2 * c + b + a)) ≥ 9 / 4   :=  by sorry
