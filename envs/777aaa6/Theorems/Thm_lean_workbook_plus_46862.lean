-- Prove2me | Theorems.Thm_lean_workbook_plus_46862
-- name    : lean_workbook_plus_46862
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/fc7272e2-83f6-4fc6-9b75-4ad10b49632a
-- statement:
--   Prove that $x^2 + y^2 + z^2 \geq xy + yz + xz$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46862 (x y z : ℝ) : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + y * z + x * z   :=  by sorry
