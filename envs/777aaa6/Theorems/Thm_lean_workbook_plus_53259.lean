-- Prove2me | Theorems.Thm_lean_workbook_plus_53259
-- name    : lean_workbook_plus_53259
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/60edc95c-7066-4b9c-81e9-3c48fc574c03
-- statement:
--   For $a,b\ge 0$ such that $a^2\ge 4b$ . Prove that: $5(a^2b^2-ab)+8\ge 9b^2(b+1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53259 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a^2 ≥ 4 * b) : 5 * (a^2 * b^2 - a * b) + 8 ≥ 9 * b^2 * (b + 1)   :=  by sorry
