-- Prove2me | Theorems.Thm_lean_workbook_plus_15268
-- name    : lean_workbook_plus_15268
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/85eb634e-13e8-45d6-a954-a78872def7ff
-- statement:
--   prove: $x^2+y^2+z^2\geq 3$ given $x+y+z=3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15268 (x y z : ℝ) (h : x + y + z = 3) : x ^ 2 + y ^ 2 + z ^ 2 ≥ 3   :=  by sorry
