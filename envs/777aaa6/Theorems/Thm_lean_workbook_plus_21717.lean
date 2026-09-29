-- Prove2me | Theorems.Thm_lean_workbook_plus_21717
-- name    : lean_workbook_plus_21717
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/be42e34c-8548-4ad2-9f2a-73f978f10f36
-- statement:
--   Prove that $\frac{a}{a+bc}+\frac{c}{b+ca}+\frac{b}{c+ab} \leq \frac{9}{4}$ given $a,b,c>0$ and $a+b+c=1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21717 : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b + c = 1 → a / (a + b * c) + c / (b + a * c) + b / (c + a * b) ≤ 9 / 4   :=  by sorry
