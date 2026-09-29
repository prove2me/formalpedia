-- Prove2me | Theorems.Thm_lean_workbook_plus_58757
-- name    : lean_workbook_plus_58757
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/75a707b5-8414-40d6-b43f-21035571a442
-- statement:
--   $\frac{a}{b+c}+\frac{b}{c+a}+\frac{c}{a+b}<2 \Box$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58757 : ∀ a b c : ℝ, (a / (b + c) + b / (c + a) + c / (a + b) < 2)   :=  by sorry
