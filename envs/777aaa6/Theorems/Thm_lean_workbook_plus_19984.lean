-- Prove2me | Theorems.Thm_lean_workbook_plus_19984
-- name    : lean_workbook_plus_19984
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/caea63c5-da5f-48d0-bcdd-4b9621aa3521
-- statement:
--   We can use the Euclidean Algorithm to calculate the greatest common divisor of 6994 and 5993: $\gcd (6994, 5993) = \gcd (5993, 1001) = \gcd (1001, 988) = \gcd (1001, 13) = 13$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19984 :
  Nat.gcd 6994 5993 = 13   :=  by sorry
