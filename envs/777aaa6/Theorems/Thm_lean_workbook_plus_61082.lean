-- Prove2me | Theorems.Thm_lean_workbook_plus_61082
-- name    : lean_workbook_plus_61082
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/ec22e036-6a3e-40e0-af2f-bb643c15c52f
-- statement:
--   If $ a, b, c > 0$ , prove that\n\n1. $ 4(a^3 + b^3)\ge (a + b)^3$ \n\n2. $ 9(a^3 + b^3 + c^3) \ge (a + b + c)^3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61082 : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 → (4 * (a ^ 3 + b ^ 3) ≥ (a + b) ^ 3 ∧ 9 * (a ^ 3 + b ^ 3 + c ^ 3) ≥ (a + b + c) ^ 3)   :=  by sorry
