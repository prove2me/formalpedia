-- Prove2me | Theorems.Thm_lean_workbook_plus_53961
-- name    : lean_workbook_plus_53961
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/f5962fa4-2576-4a49-b1c1-9197bf8f763f
-- statement:
--   Prove $3(x^2-x+1)^3 \geq x^6+x^3+1$ for positive reals.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53961 (x : ℝ) (hx : 0 < x) : 3 * (x ^ 2 - x + 1) ^ 3 ≥ x ^ 6 + x ^ 3 + 1   :=  by sorry
