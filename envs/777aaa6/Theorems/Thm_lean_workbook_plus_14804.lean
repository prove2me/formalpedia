-- Prove2me | Theorems.Thm_lean_workbook_plus_14804
-- name    : lean_workbook_plus_14804
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/35c7a5b3-599d-48f4-b3fa-27bca5b0dfbe
-- statement:
--   Prove that $x(x-1)^2\geq 0$ for $0\leq x\leq 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14804 (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) :
  x * (x - 1) ^ 2 ≥ 0   :=  by sorry
