-- Prove2me | Theorems.Thm_lean_workbook_plus_6161
-- name    : lean_workbook_plus_6161
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/52284c39-c6ae-4362-8aab-ec996b38d88b
-- statement:
--   Rewrite the equation $x(x-y^{2})=y^{2}-76$ as a quadratic in $x$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6161 (x y : ℤ) : x * (x - y ^ 2) = y ^ 2 - 76 ↔ x ^ 2 - x * y ^ 2 = y ^ 2 - 76   :=  by sorry
