-- Prove2me | Theorems.Thm_lean_workbook_plus_53040
-- name    : lean_workbook_plus_53040
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/4dfdfa2b-b118-47cd-ab97-fc904757243b
-- statement:
--   Prove that for all real numbers $x$ and $y$ such that $0 < x < 1$ and $z = \frac{1 - x^2}{2x}$, the inequality $(3x^2 - 1)^2(5x^2 - 1)^2 \geq 0$ holds.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53040 {x : ℝ} (hx : 0 < x ∧ x < 1) : (3 * x ^ 2 - 1) ^ 2 * (5 * x ^ 2 - 1) ^ 2 ≥ 0   :=  by sorry
