-- Prove2me | Theorems.Thm_lean_workbook_plus_15689
-- name    : lean_workbook_plus_15689
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/88bfe0df-dd14-4bc1-a875-ead395febdc2
-- statement:
--   For all real numbers $a,b,c>0$ . Prove that \n $$\frac{a}{(1+a)^3}+\frac{b}{(1+b)^3}+\frac{c}{(1+c)^3}\leq \frac{3}{8}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15689 : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → a / (1 + a) ^ 3 + b / (1 + b) ^ 3 + c / (1 + c) ^ 3 ≤ 3 / 8   :=  by sorry
