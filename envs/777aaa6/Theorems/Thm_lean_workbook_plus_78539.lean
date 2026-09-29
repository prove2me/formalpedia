-- Prove2me | Theorems.Thm_lean_workbook_plus_78539
-- name    : lean_workbook_plus_78539
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/958d335e-34d5-420c-9735-da6a2d72e3bd
-- statement:
--   Let $sinx+siny=\frac{1}{3},cosx-cosy=\frac{1}{5}$ , find the value of $sin(x-y)$ and $cos(x+y)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78539 (x y : ℝ) (h₁ : sin x + sin y = 1/3) (h₂ : cos x - cos y = 1/5) : sin (x - y) = 7/15 ∧ cos (x + y) = 7/15   :=  by sorry
