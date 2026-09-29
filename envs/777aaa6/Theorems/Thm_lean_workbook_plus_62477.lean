-- Prove2me | Theorems.Thm_lean_workbook_plus_62477
-- name    : lean_workbook_plus_62477
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/c26c2b0b-39bf-470a-9703-dc6738979a79
-- statement:
--   The discriminant $D = 4g^2 - 4c < 0$ implies $g^2 < c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62477 {g c : ℝ} (h : 4 * g ^ 2 - 4 * c < 0) : g ^ 2 < c   :=  by sorry
