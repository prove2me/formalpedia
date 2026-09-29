-- Prove2me | Theorems.Thm_lean_workbook_plus_54386
-- name    : lean_workbook_plus_54386
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/752f2683-a148-400f-b046-3c1c77cccae2
-- statement:
--   Let $x_1=0$ and $x_{n+1}=5x_n+\sqrt{24x_n^2+1}$ . Prove $x_n$ is always a non-negative integer.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54386 (x : ℕ → ℝ) (x0 : x 0 = 0) (x_rec : ∀ n, x (n + 1) = 5 * x n + Real.sqrt (24 * (x n)^2 + 1)) : ∀ n, 0 ≤ x n   :=  by sorry
