-- Prove2me | Theorems.Thm_lean_workbook_plus_74935
-- name    : lean_workbook_plus_74935
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/4acdf21f-5ad7-4f25-b4d5-891ef83d81eb
-- statement:
--   Prove that there is no bijection from $\mathbb R\to\mathbb R$ such that $f(x)f^{-1}(x)=1$ $\forall x\in\mathbb R$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74935 : ¬∃ f : ℝ → ℝ, Function.Bijective f ∧ ∀ x : ℝ, f x * f⁻¹ x = 1   :=  by sorry
