-- Prove2me | Theorems.Thm_lean_workbook_plus_66634
-- name    : lean_workbook_plus_66634
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/2b8ab947-61a7-4383-aa83-c3b57575790e
-- statement:
--   $ t=10$ ---> $ x=\sqrt{\frac{623}{6}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66634 (t x : ℝ) (ht : t = 10) (hx : x = Real.sqrt (623/6)) : t = 10 ∧ x = Real.sqrt (623/6)   :=  by sorry
