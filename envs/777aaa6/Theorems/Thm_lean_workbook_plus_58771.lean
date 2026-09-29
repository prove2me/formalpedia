-- Prove2me | Theorems.Thm_lean_workbook_plus_58771
-- name    : lean_workbook_plus_58771
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/5cb19592-8986-44b0-a203-7f631f72ddf9
-- statement:
--   If $a_1\ge a_2\ge a_3, \ b_1\ge b_2\ge b_3$ then Chebyshev says: \n\n $a_1b_1+a_2b_2+a_3b_3\ge \frac{1}{3}(a_1+a_2+a_3)(b_1+b_2+b_3)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58771 (a b : ℕ → ℕ) (h₁ : a 1 ≥ a 2 ∧ a 2 ≥ a 3) (h₂ : b 1 ≥ b 2 ∧ b 2 ≥ b 3) : a 1 * b 1 + a 2 * b 2 + a 3 * b 3 ≥ 1 / 3 * (a 1 + a 2 + a 3) * (b 1 + b 2 + b 3)   :=  by sorry
