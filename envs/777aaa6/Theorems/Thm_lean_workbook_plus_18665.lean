-- Prove2me | Theorems.Thm_lean_workbook_plus_18665
-- name    : lean_workbook_plus_18665
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/657b8441-371d-47be-b14e-43c7cb3bbd4e
-- statement:
--   Let be $ a,b,c\in \mathbb{R}$ such that $ ab + bc + ca + abc = a^2 + b^2 + c^2$ . Prove that $ a,b,c$ can't all be nonpositives .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18665 : ∀ a b c : ℝ, a * b + b * c + c * a + a * b * c = a ^ 2 + b ^ 2 + c ^ 2 → ¬(a ≤ 0 ∧ b ≤ 0 ∧ c ≤ 0)   :=  by sorry
