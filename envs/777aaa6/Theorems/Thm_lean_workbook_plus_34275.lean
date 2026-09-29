-- Prove2me | Theorems.Thm_lean_workbook_plus_34275
-- name    : lean_workbook_plus_34275
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/53cacabe-c7d5-44ab-98b1-038c12517bb6
-- statement:
--   Let $ a \leq b \leq c$ . Prove that: \n $ 3a \leq a + b + c - \sqrt {a^2 + b^2 + c^2 - ab - bc - ca}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34275 : ∀ a b c : ℝ, a ≤ b ∧ b ≤ c → 3 * a ≤ a + b + c - Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a)   :=  by sorry
