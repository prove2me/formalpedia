-- Prove2me | Theorems.Thm_lean_workbook_plus_51466
-- name    : lean_workbook_plus_51466
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/ca636a66-a5f7-49b5-bc52-aaf87776d31c
-- statement:
--   Is it true that $ a^2+b^2+c^2+d^2-ab-ac-ad-bc-bd-cd\geq0$ given the condition that $ a\leq 0\leq b\leq c\leq d$ and the fact that $ a+b\geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51466 (a b c d : ℝ) (h₁ : a ≤ 0 ∧ 0 ≤ b ∧ b ≤ c ∧ c ≤ d) (h₂ : a + b ≥ 0) : a^2 + b^2 + c^2 + d^2 - a * b - a * c - a * d - b * c - b * d - c * d ≥ 0   :=  by sorry
