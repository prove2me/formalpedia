-- Prove2me | Theorems.Thm_lean_workbook_plus_77674
-- name    : lean_workbook_plus_77674
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/f3fd5d79-a3c7-4f3c-8944-de75fd84fc93
-- statement:
--   Let $a,b,c>0$ , and such: $a^2+b^2+c^2=3$ . Prove: $\dfrac{a^4}{\sqrt{b^3+7}}+\dfrac{b^4}{\sqrt{c^3+7}}+\dfrac{c^4}{\sqrt{a^3+7}}\ge \dfrac{3}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77674 : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a^2 + b^2 + c^2 = 3 → a^4 / Real.sqrt (b^3 + 7) + b^4 / Real.sqrt (c^3 + 7) + c^4 / Real.sqrt (a^3 + 7) ≥ 3 / 2   :=  by sorry
