-- Prove2me | Theorems.Thm_lean_workbook_plus_55094
-- name    : lean_workbook_plus_55094
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/16bccf89-b0b9-4df9-a8c1-b36c5e55edd1
-- statement:
--   Prove that $(ab+bc+ca+abc)\left(\frac{1}{(a+b)^3}+\frac{1}{(b+c)^3}+\frac{1}{(c+a)^3}\right) \ge \frac{51}{28}$, given $a,b,c\ge 0$ and $a+b+c=\frac{7}{3}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55094 :  ∀ a b c : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ a + b + c = 7 / 3 → (a * b + b * c + c * a + a * b * c) * (1 / (a + b) ^ 3 + 1 / (b + c) ^ 3 + 1 / (c + a) ^ 3) ≥ 51 / 28   :=  by sorry
