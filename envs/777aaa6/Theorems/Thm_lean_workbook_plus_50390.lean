-- Prove2me | Theorems.Thm_lean_workbook_plus_50390
-- name    : lean_workbook_plus_50390
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/29ab8278-8456-414b-aa3d-9e80991898ac
-- statement:
--   That makes the answer $13^2+12^2+11^2+10^2+9^2+8^2+7^2+6^2+5^2+4^2+3^2+2^2+1^2=\boxed{819}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50390 :
  ∑ i in Finset.range 13, (13 - i)^2 = 819   :=  by sorry
