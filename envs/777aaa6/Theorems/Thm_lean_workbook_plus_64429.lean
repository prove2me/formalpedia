-- Prove2me | Theorems.Thm_lean_workbook_plus_64429
-- name    : lean_workbook_plus_64429
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/d683ea90-e678-473d-8939-356309c458cf
-- statement:
--   Prove that $\dfrac{1}{a}-\dfrac{1}{b}=\dfrac{b-a}{ab}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64429 (a b : ℝ) : a ≠ 0 ∧ b ≠ 0 → 1/a - 1/b = (b - a)/(a * b)   :=  by sorry
