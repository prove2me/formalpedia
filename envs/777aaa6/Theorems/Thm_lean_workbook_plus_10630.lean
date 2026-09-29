-- Prove2me | Theorems.Thm_lean_workbook_plus_10630
-- name    : lean_workbook_plus_10630
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/618fd33d-ecd8-4729-b403-2971eebf065a
-- statement:
--   By Cauchy-Schwarz we have: $\frac{1}{4b^2+a^2+4c^2}=\frac{(a+b+c)^2}{3c^2+(a^2+c^2+b^2)+3b^2}\leq \frac{c}{3}+\frac{b}{3}+\frac{a^2}{a^2+b^2+c^2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10630 ∀ a b c : ℝ, (1 / (4 * b ^ 2 + a ^ 2 + 4 * c ^ 2) ≤ c / 3 + b / 3 + a ^ 2 / (a ^ 2 + b ^ 2 + c ^ 2))   :=  by sorry
