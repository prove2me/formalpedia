-- Prove2me | Theorems.Thm_lean_workbook_plus_67017
-- name    : lean_workbook_plus_67017
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/8f0108f5-383c-4521-bf18-be91ef5d8a9c
-- statement:
--   Let $a,b,c\geq \frac{4}{3}.$ Prove that $a+b+c\geq \frac{2}{a}+ \frac{1}{b}+ \frac{1}{c}+1 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67017 (a b c : ℝ) (ha : a ≥ 4/3 ∧ b ≥ 4/3 ∧ c ≥ 4/3) : a + b + c ≥ 2/a + 1/b + 1/c + 1   :=  by sorry
