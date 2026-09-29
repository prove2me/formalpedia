-- Prove2me | Theorems.Thm_lean_workbook_plus_32045
-- name    : lean_workbook_plus_32045
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/797fcc34-5258-4c70-a145-2c2c741bcc27
-- statement:
--   If $a\\cdot\\frac{1}{b}=1, b\\cdot\\frac{1}{c}=1$, then $c\\cdot\\frac{1}{a}=1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32045 (a b c : ℝ) (h₁ : a * (1/b) = 1) (h₂ : b * (1/c) = 1) : c * (1/a) = 1   :=  by sorry
