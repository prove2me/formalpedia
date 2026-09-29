-- Prove2me | Theorems.Thm_lean_workbook_plus_51658
-- name    : lean_workbook_plus_51658
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/7d8d620e-425d-4f96-a0d1-7e5bc49f0664
-- statement:
--   $\sqrt{ab} \le \frac{\sqrt{3}a+\frac{b}{\sqrt{3}}}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51658 : ∀ a b : ℝ, Real.sqrt (a * b) ≤ (Real.sqrt 3 * a + b / Real.sqrt 3) / 2   :=  by sorry
