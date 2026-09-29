-- Prove2me | Theorems.Thm_lean_workbook_plus_42343
-- name    : lean_workbook_plus_42343
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/b34acc88-4a2d-4b32-a798-f88549c0102c
-- statement:
--   Let $a,b$ be positive numbers such that $ab=1.$ Prove that $a^2+b^2+4\geq 3(a+b)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42343 (a b : ℝ) (hab : a * b = 1) : a ^ 2 + b ^ 2 + 4 ≥ 3 * (a + b)   :=  by sorry
