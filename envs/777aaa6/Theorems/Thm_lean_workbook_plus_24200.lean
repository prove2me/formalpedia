-- Prove2me | Theorems.Thm_lean_workbook_plus_24200
-- name    : lean_workbook_plus_24200
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/aafc39ea-77e1-496d-bf30-8902cad3f31d
-- statement:
--   Prove or disprove that $\left(\frac{a}{a+b}\right)^{3}+\left(\frac{b}{b+c}\right)^{3}+\left(\frac{c}{c+a}\right)^{3}\leq \frac{9}{8}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24200 : ∀ a b c : ℝ, (a / (a + b)) ^ 3 + (b / (b + c)) ^ 3 + (c / (c + a)) ^ 3 ≤ 9 / 8   :=  by sorry
