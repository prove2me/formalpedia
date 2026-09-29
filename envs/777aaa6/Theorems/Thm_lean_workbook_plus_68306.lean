-- Prove2me | Theorems.Thm_lean_workbook_plus_68306
-- name    : lean_workbook_plus_68306
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/db1e97a3-b492-4d6c-a689-67ba7f5d37e9
-- statement:
--   Prove that for a, b, c being the lengths of the sides of a triangle, the following inequality holds: $a^3 + b^3 + c^3 - 2[a^2(b + c) + b^2(a + c) + c^2(a + b)] \leq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68306 (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : a ^ 3 + b ^ 3 + c ^ 3 - 2 * (a ^ 2 * (b + c) + b ^ 2 * (a + c) + c ^ 2 * (a + b)) ≤ 0   :=  by sorry
