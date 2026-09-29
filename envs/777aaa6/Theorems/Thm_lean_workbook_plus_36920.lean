-- Prove2me | Theorems.Thm_lean_workbook_plus_36920
-- name    : lean_workbook_plus_36920
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/67dacb5b-c9f7-489e-9289-8ef168eb7b2f
-- statement:
--   How many positive divisors does $72$ have?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36920 :
  (∑ k in (Nat.divisors 72), 1) = 12   :=  by sorry
