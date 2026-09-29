-- Prove2me | Theorems.Thm_lean_workbook_plus_72085
-- name    : lean_workbook_plus_72085
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/1dd397cc-e649-4b77-9754-06511d43900b
-- statement:
--   At the maximum elongation(called amplitude) all of this K.E is converted into spring Potential Energy(U). $ U = \frac12 kA^2$ . In both cases U is same. and $ k_2 = 2k \implies A_2 = \frac {A}{\sqrt2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72085 (A : ℝ) (k : ℝ) (U : ℝ) (h₁ : U = 1 / 2 * k * A ^ 2) (h₂ : k_2 = 2 * k) (h₃ : A_2 = A / Real.sqrt 2) : U = 1 / 2 * k_2 * A_2 ^ 2   :=  by sorry
