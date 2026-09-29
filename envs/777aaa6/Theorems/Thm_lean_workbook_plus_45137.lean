-- Prove2me | Theorems.Thm_lean_workbook_plus_45137
-- name    : lean_workbook_plus_45137
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/4acce104-b003-4e64-9df6-4d62035fc9b2
-- statement:
--   Prove that $x^3\geq4x-3, \forall x\in [0;1].$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45137 {x : ℝ} (hx : 0 ≤ x ∧ x ≤ 1) : x^3 ≥ 4 * x - 3   :=  by sorry
