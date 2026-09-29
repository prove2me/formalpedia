-- Prove2me | Theorems.Thm_lean_workbook_plus_13634
-- name    : lean_workbook_plus_13634
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/89736ef5-8b2d-469e-81f4-5cf4be6b6dea
-- statement:
--   Let $ x, y, z$ be nonnegative reals such that $ x + y + z\geq 5$ . Prove that at least two of the following three inequalities \n\n $ 2x + 3y + 6z\geq 14 , 2y + 3z + 6x\geq 14,2z + 3x + 6y\geq 14$ \n\n are true.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13634 (x y z : ℝ) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) (h : x + y + z ≥ 5) : ∃ i j : Fin 3, i ≠ j ∧ (2 * x + 3 * y + 6 * z ≥ 14 ∨ 2 * y + 3 * z + 6 * x ≥ 14 ∨ 2 * z + 3 * x + 6 * y ≥ 14)   :=  by sorry
