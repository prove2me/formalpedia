-- Prove2me | Theorems.Thm_lean_workbook_plus_29442
-- name    : lean_workbook_plus_29442
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/d7180438-099d-4ddd-bef7-0e65311a3cb3
-- statement:
--   Let $a, b \ge 1.$ Prove that $ab(a + b - 10) + 8(a + b)\geq 8$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29442 (a b : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) : a * b * (a + b - 10) + 8 * (a + b) ≥ 8   :=  by sorry
