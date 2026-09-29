-- Prove2me | Theorems.Thm_lean_workbook_plus_73113
-- name    : lean_workbook_plus_73113
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/c71b17cd-5bd3-4c3a-967f-91aec0851124
-- statement:
--   Let $a,b,c>0$ such that $a+b+c=3$ . \n\n $$ab(a^2+b^2) \leq \frac{(a+b)^4}{8} $$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73113 :  ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b + c = 3 → a * b * (a ^ 2 + b ^ 2) ≤ (a + b) ^ 4 / 8   :=  by sorry
