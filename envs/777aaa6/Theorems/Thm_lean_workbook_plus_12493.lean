-- Prove2me | Theorems.Thm_lean_workbook_plus_12493
-- name    : lean_workbook_plus_12493
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/686391ac-91b5-4bcd-bbd5-9b749e99cc45
-- statement:
--   Prove that $\frac{a}{b^2+c}+\frac{b}{c^2+a}+\frac{c}{a^2+b}\ge\frac{9}{4}$ given $a+b+c=1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12493 : ∀ a b c : ℝ, a + b + c = 1 → a / (b ^ 2 + c) + b / (c ^ 2 + a) + c / (a ^ 2 + b) ≥ 9 / 4   :=  by sorry
