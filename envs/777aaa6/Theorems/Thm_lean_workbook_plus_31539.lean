-- Prove2me | Theorems.Thm_lean_workbook_plus_31539
-- name    : lean_workbook_plus_31539
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/342852a6-221e-4f4b-a9b3-ae6d7dfe6c32
-- statement:
--   Since $a,b,c,d \in [1;3]$ , then $(a-1)(b-1)(c-1) \ge 0$ and $(3-a)(3-b)(3-c) \ge 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31539 (a b c d : ℝ) (hab : 1 ≤ a ∧ a ≤ 3) (hbc : 1 ≤ b ∧ b ≤ 3) (hcd : 1 ≤ c ∧ c ≤ 3) : (a - 1) * (b - 1) * (c - 1) ≥ 0 ∧ (3 - a) * (3 - b) * (3 - c) ≥ 0   :=  by sorry
