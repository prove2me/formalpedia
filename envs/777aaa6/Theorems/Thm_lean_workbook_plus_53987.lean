-- Prove2me | Theorems.Thm_lean_workbook_plus_53987
-- name    : lean_workbook_plus_53987
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/249027cc-6d66-486c-86a0-f01e8c9e9d22
-- statement:
--   Given $a, b, c$ are real numbers such that $a + b + c = 3$, prove that $(3 - a)(3 - b)(3 - c) \geq 8abc$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53987 : ∀ a b c : ℝ, a + b + c = 3 → (3 - a) * (3 - b) * (3 - c) ≥ 8 * a * b * c   :=  by sorry
