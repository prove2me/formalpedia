-- Prove2me | Theorems.Thm_lean_workbook_plus_82040
-- name    : lean_workbook_plus_82040
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/2ef5c177-e7cb-4243-adee-ddf9f1b88114
-- statement:
--   What is the intersection of the lines given by $2y=-x+3$ and $-y=5x+1$ ? Enter the answer as an ordered pair.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82040 (x y : ℝ) : (2*y = -x + 3 ∧ -y = 5*x + 1) ↔ (x = -5/9 ∧ y = 16/9)   :=  by sorry
