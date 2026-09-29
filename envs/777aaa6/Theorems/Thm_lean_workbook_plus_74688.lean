-- Prove2me | Theorems.Thm_lean_workbook_plus_74688
-- name    : lean_workbook_plus_74688
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/dd0737d1-7b69-4836-80f9-ba8006e7f191
-- statement:
--   Given $a+b+c=1$, prove that $\frac{a}{(b+c)^2}+\frac{b}{(c+a)^2}+\frac{c}{(a+b)^2}\ge \frac{9}{4}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74688 : ∀ a b c : ℝ, a + b + c = 1 → a / (b + c) ^ 2 + b / (c + a) ^ 2 + c / (a + b) ^ 2 >= 9 / 4   :=  by sorry
