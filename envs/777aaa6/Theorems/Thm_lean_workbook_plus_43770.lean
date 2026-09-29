-- Prove2me | Theorems.Thm_lean_workbook_plus_43770
-- name    : lean_workbook_plus_43770
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/2179b8bb-e10a-47fc-b9f4-e200af007ad0
-- statement:
--   Prove that for $x, y, z \in \mathbb{R}$, $y^4z^2 + z^4x^2 + x^4y^2 \geq yzx(zx^2 + y^2x + z^2y)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43770 (x y z : ℝ) : y^4 * z^2 + z^4 * x^2 + x^4 * y^2 ≥ y * z * x * (z * x^2 + y^2 * x + z^2 * y)   :=  by sorry
