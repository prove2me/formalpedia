-- Prove2me | Theorems.Thm_lean_workbook_plus_71420
-- name    : lean_workbook_plus_71420
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/33359cb8-504a-48eb-b8ef-99c438e1089e
-- statement:
--   Prove that U is a linear subspace $U=\left \\{ f\\in \\mathbb{R}^{\\mathbb{R}} \\mid f(x)=f(-x),\\forall \\in \\mathbb{R}\\right \\}$ is a linear subspace in $\\mathbb{R}^{\\mathbb{R}}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71420 (U : Set (ℝ → ℝ)) (hU : U = {f : ℝ → ℝ | ∀ x, f x = f (-x)}) : (∀ f g : ℝ → ℝ, f ∈ U ∧ g ∈ U → f + g ∈ U) ∧ (∀ f : ℝ → ℝ, f ∈ U → ∀ c : ℝ, c • f ∈ U)   :=  by sorry
