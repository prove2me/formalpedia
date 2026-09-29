-- Prove2me | Theorems.Thm_lean_workbook_plus_5108
-- name    : lean_workbook_plus_5108
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/5abfbb7d-aa55-48c9-86f1-ec3d6d3ea1db
-- statement:
--   From $a^2+b^2+c^2=1$ we have $a^2,b^2,c^2<=1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5108 (a b c : ℝ) (h : a^2 + b^2 + c^2 = 1) : a^2 <= 1 ∧ b^2 <= 1 ∧ c^2 <= 1   :=  by sorry
