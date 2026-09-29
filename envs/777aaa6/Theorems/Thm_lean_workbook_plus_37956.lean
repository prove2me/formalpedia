-- Prove2me | Theorems.Thm_lean_workbook_plus_37956
-- name    : lean_workbook_plus_37956
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/a684c5f9-e95a-4ba6-b132-b7b472ed4aa2
-- statement:
--   Let $a,b,c\ge 0$ and $a^2+2b^2+c^2=a^3+2b^3+c^3$ . Prove that \n $$a+2b+c\leq 4$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37956 (a b c : ℝ) (ha : a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0) (hab : a^2 + 2 * b^2 + c^2 = a^3 + 2 * b^3 + c^3) : a + 2 * b + c ≤ 4   :=  by sorry
