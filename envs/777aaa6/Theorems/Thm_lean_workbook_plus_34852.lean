-- Prove2me | Theorems.Thm_lean_workbook_plus_34852
-- name    : lean_workbook_plus_34852
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/9e9874c7-3945-4f2e-8436-f4cbbe37e742
-- statement:
--   Given $x, y, z \in \mathbb{R}^+$ such that $x^2 + y^2 + z^2 + xyz = 4$. Prove that $x^2 + y^2 + z^2 \leq 4 + x^2y + y^2z + z^2x$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34852 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x^2 + y^2 + z^2 + x * y * z = 4) : x^2 + y^2 + z^2 ≤ 4 + x^2 * y + y^2 * z + z^2 * x   :=  by sorry
