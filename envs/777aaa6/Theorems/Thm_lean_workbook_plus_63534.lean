-- Prove2me | Theorems.Thm_lean_workbook_plus_63534
-- name    : lean_workbook_plus_63534
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/7c9bb2f7-6202-4b1e-a424-796e11214292
-- statement:
--   Let $a, b, c$ be the side lengths of a triangle. Prove that $2 (a^3 + b^3 + c^3) < (a + b + c) (a^2 + b^2 + c^2) \le 3 (a^3 + b^3 + c^3)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63534 {a b c : ℝ} (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : 2 * (a^3 + b^3 + c^3) < (a + b + c) * (a^2 + b^2 + c^2) ∧ (a + b + c) * (a^2 + b^2 + c^2) ≤ 3 * (a^3 + b^3 + c^3)   :=  by sorry
