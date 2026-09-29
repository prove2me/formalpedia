-- Prove2me | Theorems.Thm_lean_workbook_plus_45123
-- name    : lean_workbook_plus_45123
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/9fb1ce69-85a3-44c7-b346-402cb6206776
-- statement:
--   Let $a,b,c\geq 0 $ and $\frac{a}{a+1}+\frac{3b}{b+1}+\frac{3c}{c+1}=1 .$ Prove that $abc\leq \frac{1}{120}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45123 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a * b * c = 1) : a / (a + 1) + 3 * b / (b + 1) + 3 * c / (c + 1) = 1 → a * b * c ≤ 1 / 120   :=  by sorry
