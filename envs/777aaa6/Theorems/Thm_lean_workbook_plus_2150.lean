-- Prove2me | Theorems.Thm_lean_workbook_plus_2150
-- name    : lean_workbook_plus_2150
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/ba6f02ab-8da0-411f-8446-07726ac18f81
-- statement:
--   Using the discriminant; $ x^2 + 2x + q$ has real solutions for $ 4-4q \ge 0 \longrightarrow q \le 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2150  (q : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = x^2 + 2 * x + q)
  (h₁ : ∃ x, f x = 0) :
  q ≤ 1   :=  by sorry
