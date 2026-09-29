-- Prove2me | Theorems.Thm_lean_workbook_plus_49431
-- name    : lean_workbook_plus_49431
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/dee4a41c-bd6a-4d27-94cc-c3ae9d80f7dd
-- statement:
--   If $x, y \in \mathbb{R}$ and $y > 0$, prove that $4(x^2 + y^2)^2 \ge y^2(7x^2 + 3xy + 3y^2)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49431 (x y : ℝ) (hy : 0 < y) : 4 * (x ^ 2 + y ^ 2) ^ 2 ≥ y ^ 2 * (7 * x ^ 2 + 3 * x * y + 3 * y ^ 2)   :=  by sorry
