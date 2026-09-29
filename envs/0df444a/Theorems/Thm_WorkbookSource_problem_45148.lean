-- Prove2me | Theorems.Thm_WorkbookSource_problem_45148
-- name    : WorkbookSource.problem_45148
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:50:45.651355+00:00
-- url     : https://prove2.me/theorems/ff225a6e-44d0-4c47-9c2e-4dab3e7bb4d8
-- title:
--   A cubic inequality on the unit interval
-- statement:
--   Given the inequality \(4(x^3 + 1) \geq (x + 1)^3 - (x - 1)^3\) for \(x \in [0, 1)\), prove that it is true.
--
--   Source: InternLM Lean-Workbook, record lean_workbook_45148; Apache-2.0. Complete source proposition preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_45148; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_45148 (x : ℝ) (hx : 0 ≤ x ∧ x < 1) :
  4 * (x^3 + 1) ≥ (x + 1)^3 - (x - 1)^3  :=  by sorry
