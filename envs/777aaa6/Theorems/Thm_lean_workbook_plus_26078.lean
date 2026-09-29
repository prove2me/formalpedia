-- Prove2me | Theorems.Thm_lean_workbook_plus_26078
-- name    : lean_workbook_plus_26078
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/ee217e5b-ccff-4348-90df-829f9edb1a4f
-- statement:
--   Prove that if $f : \mathbb{R} \to \mathbb{R}$ is a continuous function such that $f(f(x)) = x$ for all $x \in \mathbb{R}$, then $f$ is bijective.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26078 (f : ℝ → ℝ) (hf : Continuous f) (h : ∀ x, f (f x) = x) : Function.Bijective f   :=  by sorry
