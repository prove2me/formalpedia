-- Prove2me | Theorems.Thm_lean_workbook_plus_12467
-- name    : lean_workbook_plus_12467
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/34bf3f38-ec35-467c-a433-866ba7266be4
-- statement:
--   ${n^2+x^2\over 2}=\left({n+x\over 2}\right)^2+\left({n-x\over 2}\right)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12467  (n x : ℝ) :
  (n^2 + x^2) / 2 = ((n + x) / 2)^2 + ((n - x) / 2)^2   :=  by sorry
