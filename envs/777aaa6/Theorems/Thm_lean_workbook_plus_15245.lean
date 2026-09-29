-- Prove2me | Theorems.Thm_lean_workbook_plus_15245
-- name    : lean_workbook_plus_15245
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/3aecdf71-2d94-4106-b050-53add257a851
-- statement:
--   Prove that $x(x-6)^2\leq36$ when $0\leq x\leq6$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15245 (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 6) :
  x * (x - 6) ^ 2 ≤ 36   :=  by sorry
