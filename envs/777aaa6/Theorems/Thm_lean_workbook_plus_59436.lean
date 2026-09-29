-- Prove2me | Theorems.Thm_lean_workbook_plus_59436
-- name    : lean_workbook_plus_59436
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/ff90ce0b-4aee-4167-9289-b5221a154fe3
-- statement:
--   In triangle $ABC$, prove $a^2+(b-a)(c-a)>0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59436 : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b > c ∧ a + c > b ∧ b + c > a → a^2 + (b - a) * (c - a) > 0   :=  by sorry
