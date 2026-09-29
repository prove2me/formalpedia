-- Prove2me | Theorems.Thm_lean_workbook_plus_54147
-- name    : lean_workbook_plus_54147
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/9633b228-d61d-494a-b411-0da56fc88c11
-- statement:
--   Derive $|g(x)| > \frac{|M|}{2}$ from $|g(x) - M| < \frac{|M|}{2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54147 (M x: ℝ) (g : ℝ → ℝ) (h₁ : |g x - M| < |M| / 2) : |g x| > |M| / 2   :=  by sorry
