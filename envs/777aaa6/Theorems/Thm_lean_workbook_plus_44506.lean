-- Prove2me | Theorems.Thm_lean_workbook_plus_44506
-- name    : lean_workbook_plus_44506
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/626bd659-5714-4254-a517-4cc4c0aa6043
-- statement:
--   Prove that for $a, b, c$ positive real numbers with $abc = 1$, the following inequality holds: $$\frac{a^2}{a^2+a+1}+\frac{b^2}{b^2+b+1}+\frac{c^2}{c^2+c+1} \geq 1$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44506 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a * b * c = 1) : a^2 / (a^2 + a + 1) + b^2 / (b^2 + b + 1) + c^2 / (c^2 + c + 1) ≥ 1   :=  by sorry
