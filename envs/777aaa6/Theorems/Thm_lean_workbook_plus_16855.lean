-- Prove2me | Theorems.Thm_lean_workbook_plus_16855
-- name    : lean_workbook_plus_16855
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/3c610dad-4f01-485b-b6e1-0c3578d6cea3
-- statement:
--   Let $a$ , $b$ , $c$ be real numbers such that $0 < a \le b \le c$ . Prove that $(a + 3b)(b + 4c)(c + 2a) \ge 60abc$ . When does equality hold?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16855 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : a ≤ b ∧ b ≤ c) : (a + 3 * b) * (b + 4 * c) * (c + 2 * a) ≥ 60 * a * b * c   :=  by sorry
