-- Prove2me | Theorems.Thm_lean_workbook_plus_16894
-- name    : lean_workbook_plus_16894
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/08e5549f-0907-4402-ad64-5ef0be0d13f0
-- statement:
--   Prove the equivalence of the following conditions for a symmetric polynomial of degree 3, $P(a, b, c)$: \n1) $P(1, 1, 1), P(1, 1, 0), P(1, 0, 0) \geq 0.$ \n2) $P(a, b, c) \geq 0, \forall a, b, c \geq 0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16894 (P : ℝ → ℝ → ℝ → ℝ) (h : P = fun a b c ↦ a^3 + b^3 + c^3 - 3*a*b*c) : (P 1 1 1 ≥ 0 ∧ P 1 1 0 ≥ 0 ∧ P 1 0 0 ≥ 0) ↔ (∀ a b c : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 → P a b c ≥ 0)   :=  by sorry
