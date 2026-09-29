-- Prove2me | Theorems.Thm_lean_workbook_plus_187
-- name    : lean_workbook_plus_187
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/8cefe1b4-003b-41ac-835f-2a302064e976
-- statement:
--   $$x = \frac {4-2\sqrt{3}}2 = 2 -\sqrt{3}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_187 (x : ℝ) (hx : x = (4 - 2 * Real.sqrt 3) / 2) : x = 2 - Real.sqrt 3   :=  by sorry
