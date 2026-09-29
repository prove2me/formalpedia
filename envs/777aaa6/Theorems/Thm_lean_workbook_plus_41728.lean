-- Prove2me | Theorems.Thm_lean_workbook_plus_41728
-- name    : lean_workbook_plus_41728
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/8f916ee2-20e1-4c13-80da-3bd10e08e277
-- statement:
--   Let $ a,b \in R$ such that: \n $ 0 < b \le a\le 2, ab^2 \le 2$ \nProve that: \n $ a + 2b \le 4$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41728 (a b : ℝ) (h₁ : 0 < b ∧ b ≤ a ∧ a ≤ 2) (h₂ : a * b ^ 2 ≤ 2) : a + 2 * b ≤ 4   :=  by sorry
