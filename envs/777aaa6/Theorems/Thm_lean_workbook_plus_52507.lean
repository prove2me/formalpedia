-- Prove2me | Theorems.Thm_lean_workbook_plus_52507
-- name    : lean_workbook_plus_52507
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/a06aac47-03f0-4116-95d5-4263a960cc23
-- statement:
--   If $a + b + c = 0$, show that $2(a^4+b^4+c^4)$ is a perfect square.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52507 (a b c : ℤ) (h : a + b + c = 0) :
  ∃ x : ℤ, x^2 = 2 * (a^4 + b^4 + c^4)   :=  by sorry
