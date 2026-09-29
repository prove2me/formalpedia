-- Prove2me | Theorems.Thm_lean_workbook_plus_38308
-- name    : lean_workbook_plus_38308
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/806f8b7d-c106-49b9-b67a-86b5567fcf58
-- statement:
--   Prove that if $x, y, z$ are reals, then $x^2(3y^2+3z^2-2yz) \geq yz(2xy+2xz-yz)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38308 (x y z : ℝ) : x^2 * (3 * y^2 + 3 * z^2 - 2 * y * z) ≥ y * z * (2 * x * y + 2 * x * z - y * z)   :=  by sorry
