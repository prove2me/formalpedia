-- Prove2me | Theorems.Thm_lean_workbook_plus_3518
-- name    : lean_workbook_plus_3518
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/6b91fe96-aef1-4c4e-b6a0-ef06547555bc
-- statement:
--   Prove or disprove that $\left(\frac{c}{a+c}\right)^{3}+\left(\frac{a}{a+b}\right)^{3}+\left(\frac{b}{b+c}\right)^{3}\leq \frac{9}{8}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3518 : ∀ a b c : ℝ, (c / (a + c))^3 + (a / (a + b))^3 + (b / (b + c))^3 ≤ 9 / 8   :=  by sorry
