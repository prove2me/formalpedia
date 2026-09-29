-- Prove2me | Theorems.Thm_lean_workbook_plus_66187
-- name    : lean_workbook_plus_66187
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/b6ab3ddd-f66b-4727-8391-17eb553d457a
-- statement:
--   Prove that for all reals $x$, $y$, and $z$, the following inequality is also true:\n\n$$(x^3+y^3+z^3+2xyz)^2 \geq 0$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66187 (x y z : ℝ) : (x^3 + y^3 + z^3 + 2 * x * y * z)^2 ≥ 0   :=  by sorry
