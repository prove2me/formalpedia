-- Prove2me | Theorems.Thm_lean_workbook_plus_44446
-- name    : lean_workbook_plus_44446
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/a88c70f9-6feb-4c6d-a615-0aa644d7b9e0
-- statement:
--   A function $f$ with domain $[0,1]$ and codomain $\mathbb R$ is a function $f:[0,1]\to\mathbb R$ . It is continuous iff for all $x_0\in[0,1]$ we have: $\lim_{x\to x_0}f(x)=f(x_0)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44446 (f : ℝ → ℝ) (A : Set ℝ) (hA : A = Set.Icc 0 1) :
  ContinuousOn f A ↔ ∀ x ∈ A, ContinuousWithinAt f A x   :=  by sorry
