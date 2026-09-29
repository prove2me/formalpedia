-- Prove2me | Theorems.Thm_lean_workbook_plus_6102
-- name    : lean_workbook_plus_6102
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/e71597e0-5d38-4ac8-b035-95c4326bb1a2
-- statement:
--   Does $f(x) \to M$ mean $\lim_{x \to a} f(x)=M$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6102 : ∀ f : ℝ → ℝ, ∀ a M : ℝ, (∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ x : ℝ, x ∈ Set.Ioo a δ → |f x - M| < ε) ↔ ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ x : ℝ, x ∈ Set.Ioo a δ → |f x - M| < ε   :=  by sorry
