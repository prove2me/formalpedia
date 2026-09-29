-- Prove2me | Theorems.Thm_lean_workbook_plus_63494
-- name    : lean_workbook_plus_63494
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/3b146b1d-dd39-4082-9c63-2fb09592d717
-- statement:
--   Let $a$ be a positive real number such that: $a^3= 6(a + 1)$ Prove that this equation $x^2 + ax + a^2 - 6 = 0$ doesn't have real solution.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63494 (a : ℝ) (ha : a > 0) (hab : a^3 = 6 * (a + 1)) : ¬ ∃ x : ℝ, x^2 + a * x + a^2 - 6 = 0   :=  by sorry
