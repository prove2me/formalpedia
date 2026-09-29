-- Prove2me | Theorems.Thm_lean_workbook_plus_57513
-- name    : lean_workbook_plus_57513
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/70779730-e357-4ab0-8460-46a06dd459a5
-- statement:
--   Let $ x;y;z\ge 0$ Prove that $64(x + y + z)^6\ge (x^2 + yz)(y^2 + xz)(z^2 + xy)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57513 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : 64 * (x + y + z) ^ 6 ≥ (x ^ 2 + y * z) * (y ^ 2 + x * z) * (z ^ 2 + x * y)   :=  by sorry
