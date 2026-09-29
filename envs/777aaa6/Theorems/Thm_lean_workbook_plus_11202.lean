-- Prove2me | Theorems.Thm_lean_workbook_plus_11202
-- name    : lean_workbook_plus_11202
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/68abad8f-0195-42b3-89d0-85b2a32800f2
-- statement:
--   Find the minimum of ${(\frac{a}{a+2b})}^{2}+{(\frac{b}{b+2c})}^{2}+{(\frac{c}{c+2a})}^{2}$ given $a,b,c>0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11202 (hx: a > 0 ∧ b > 0 ∧ c > 0) : 1/3 ≤ ((a / (a + 2 * b))^2 + (b / (b + 2 * c))^2 + (c / (c + 2 * a))^2)   :=  by sorry
