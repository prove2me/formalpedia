-- Prove2me | Theorems.Thm_lean_workbook_plus_42429
-- name    : lean_workbook_plus_42429
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/97dec397-7cab-4e92-8b7c-52ceee5dabd7
-- statement:
--   Let $ f$ be a constant function - say, $ f(x)=0$ for all $ x.$ Then $ f^{-1}([-1,1])=\mathbb{R}$ but $ f(f^{-1}([-1,1]))=f(\mathbb{R})=\{0\}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42429  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = 0) :
  f⁻¹' Set.Icc (-1) 1 = Set.univ ∧ f '' Set.univ = {0}   :=  by sorry
