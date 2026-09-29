-- Prove2me | Theorems.Thm_lean_workbook_plus_34658
-- name    : lean_workbook_plus_34658
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/5c4d0ffa-42b2-483e-a2eb-e5f2f5691cf7
-- statement:
--   Let $f$ be an arbitrary continuous function on $[a,b]$ and $\epsilon$ a positive number. Show that there is a polygonal function $\psi$ on $[a,b]$ with $|f(x)-\psi(x)|<\epsilon$ for all $x\in [a,b]$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34658 (f : ℝ → ℝ) (a b : ℝ) (ε : ℝ) (hf : ContinuousOn f (Set.Icc a b)) (hε : 0 < ε) : ∃ ψ : ℝ → ℝ, ContinuousOn ψ (Set.Icc a b) ∧ ∀ x ∈ Set.Icc a b, |f x - ψ x| < ε   :=  by sorry
