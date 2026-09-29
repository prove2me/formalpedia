-- Prove2me | Theorems.Thm_lean_workbook_plus_18879
-- name    : lean_workbook_plus_18879
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/b7a2d7c8-c789-4a10-9860-ca9bffb5fcf0
-- statement:
--   Find all the continuous functions $ f: [0,\infty) - > [0,\infty)$ such that $ f(f(x)) = \sqrt {xf(x)}, \forall x \in [0,\infty)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18879 (f : ℝ → ℝ) (hf: Continuous f) (h: f '' Set.Ici 0 ⊆ Set.Ici 0)(hf2: ∀ x ∈ Set.Ici 0, f (f x) = Real.sqrt (x * f x)) : ∃ g : ℝ → ℝ, Continuous g ∧ g '' Set.Ici 0 ⊆ Set.Ici 0 ∧ (∀ x ∈ Set.Ici 0, g (g x) = Real.sqrt (x * g x))   :=  by sorry
