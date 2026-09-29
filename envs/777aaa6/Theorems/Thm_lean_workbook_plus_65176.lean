-- Prove2me | Theorems.Thm_lean_workbook_plus_65176
-- name    : lean_workbook_plus_65176
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/1d1ef1e8-52d8-4d41-8d81-1b6dc201c496
-- statement:
--   Let $ a, b, c$ positive reals such that $ 0 \leq a, b, c \leq 1$ . Prove that \n\n $ (a^2b + b^2c + c^2a)(ab^2 + bc^2 + ca^2)\geq (a^2 + b^2 + c^2 - 1)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65176 : ∀ a b c : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ 0 ≤ b ∧ b ≤ 1 ∧ 0 ≤ c ∧ c ≤ 1 → (a^2 * b + b^2 * c + c^2 * a) * (a * b^2 + b * c^2 + c * a^2) ≥ (a^2 + b^2 + c^2 - 1)^2   :=  by sorry
