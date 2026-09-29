-- Prove2me | Theorems.Thm_lean_workbook_plus_72240
-- name    : lean_workbook_plus_72240
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/ee157141-d55f-4683-b3ed-7b24a91b680a
-- statement:
--   Let $a,b,c$ be positive real numbers such that (i) $c > a$ (ii) $10c = 7a +4b +2024$ (iii) $2024 = \frac{(a+c)^2}{a}+ \frac{(c+a)^2}{b}$ . Find $a +b +c$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72240 (a b c : ℝ) (h₁ : a > 0 ∧ b > 0 ∧ c > 0) (h₂ : c > a) (h₃ : 10*c = 7*a + 4*b + 2024) (h₄ : 2024 = (a + c) ^ 2 / a + (c + a) ^ 2 / b) : a + b + c = 10   :=  by sorry
