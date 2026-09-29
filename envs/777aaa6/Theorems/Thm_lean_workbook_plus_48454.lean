-- Prove2me | Theorems.Thm_lean_workbook_plus_48454
-- name    : lean_workbook_plus_48454
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/0e89bad8-97fa-4808-9628-8c0c49513231
-- statement:
--   Prove that $\sum_{cyc}(x-y)^2(x^2+2xy+7y^2)\geq0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48454 (x y z : ℝ) : (x - y) ^ 2 * (x ^ 2 + 2 * x * y + 7 * y ^ 2) + (y - z) ^ 2 * (y ^ 2 + 2 * y * z + 7 * z ^ 2) + (z - x) ^ 2 * (z ^ 2 + 2 * z * x + 7 * x ^ 2) ≥ 0   :=  by sorry
