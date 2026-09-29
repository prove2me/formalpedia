-- Prove2me | Theorems.Thm_lean_workbook_plus_39482
-- name    : lean_workbook_plus_39482
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/becc11f4-8fe1-470e-a4bb-431973e6325d
-- statement:
--   Let $ a$ , $ b$ , $ c$ be three reals such that $ c\geq b\geq a\geq 0$ . Prove that $ \left(a+3b\right)\left(b+4c\right)\left(c+2a\right)\geq 60abc$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39482 :  ∀ a b c : ℝ, c ≥ b ∧ b ≥ a ∧ a ≥ 0 → (a + 3 * b) * (b + 4 * c) * (c + 2 * a) ≥ 60 * a * b * c   :=  by sorry
