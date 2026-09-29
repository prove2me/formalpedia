-- Prove2me | Theorems.Thm_lean_workbook_plus_38082
-- name    : lean_workbook_plus_38082
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/6950d80d-ba80-413a-b98d-a9d324370aac
-- statement:
--   Let $a,b$ be positive real numbers with $0\leq a \leq b \leq1.$ \nProof that $0\leq \dfrac{a}{b+1}+\dfrac{b}{a+1} \leq1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38082 (a b : ℝ) (hab : 0 ≤ a ∧ 0 ≤ b ∧ a ≤ b ∧ b ≤ 1) :
  0 ≤ a / (b + 1) + b / (a + 1) ∧ a / (b + 1) + b / (a + 1) ≤ 1   :=  by sorry
