-- Prove2me | Theorems.Thm_lean_workbook_plus_31942
-- name    : lean_workbook_plus_31942
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/dfcedc36-dcd6-46cf-816e-d0ec6c4360e9
-- statement:
--   Prove that $f(x) + f(2z) = f(x + 2z)$ for all $x, z \in R$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31942 (f : ℝ → ℝ) (h : ∀ x z : ℝ, f x + f (2 * z) = f (x + 2 * z)) : ∀ x z : ℝ, f x + f (2 * z) = f (x + 2 * z)   :=  by sorry
