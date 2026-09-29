-- Prove2me | Theorems.Thm_lean_workbook_plus_31243
-- name    : lean_workbook_plus_31243
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/8a7e13ba-9186-40bb-ae8d-df2497120829
-- statement:
--   Prove that for $X, Y, Z \geq 0$, the following inequality holds: $X^3 + Y^3 + Z^3 + X^2Y + Y^2Z + Z^2X \geq 2(XY^2 + YZ^2 + ZX^2)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31243 (X Y Z : ℝ) (hX : X ≥ 0) (hY : Y ≥ 0) (hZ : Z ≥ 0) : X ^ 3 + Y ^ 3 + Z ^ 3 + X ^ 2 * Y + Y ^ 2 * Z + Z ^ 2 * X ≥ 2 * (X * Y ^ 2 + Y * Z ^ 2 + Z * X ^ 2)   :=  by sorry
