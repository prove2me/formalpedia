-- Prove2me | Theorems.Thm_lean_workbook_plus_54432
-- name    : lean_workbook_plus_54432
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/3c8f80f9-e322-44ad-95b6-bed6e4f58055
-- statement:
--   Prove that for positive reals $x$, $y$, and $z$, the inequality $(x+y+z)^{3}-27xyz\le 11\cdot(x^{3}+y^{3}+z^{3}-3xyz)$ holds.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54432 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y + z) ^ 3 - 27 * x * y * z ≤ 11 * (x ^ 3 + y ^ 3 + z ^ 3 - 3 * x * y * z)   :=  by sorry
