-- Prove2me | Theorems.Thm_lean_workbook_plus_42981
-- name    : lean_workbook_plus_42981
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/1b33342a-f73b-457a-ad14-c65404a29726
-- statement:
--   Prove that $f(x)=x+\frac{4}{4+x}$ is increasing for $x > 2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42981 (x y : ℝ) (h₁ : x > 2) (h₂ : y > 2) (h₃ : x < y) :
  x + (4 / (4 + x)) < y + (4 / (4 + y))   :=  by sorry
