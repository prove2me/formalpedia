-- Prove2me | Theorems.Thm_lean_workbook_plus_29081
-- name    : lean_workbook_plus_29081
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/d9675809-15ae-4734-8d55-dca5813f01bd
-- statement:
--   Prove that \n $ \frac{a}{1-a}+\frac{b}{1-b}+\frac{c}{1-c}\ge \frac{3\sqrt[3]{abc}}{1-\sqrt[3]{abc}}$ \n where $ 0<a,b,c<1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29081 (a b c : ℝ) (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1) : a / (1 - a) + b / (1 - b) + c / (1 - c) ≥ 3 * (abc)^(1/3) / (1 - (abc)^(1/3))   :=  by sorry
