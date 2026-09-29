-- Prove2me | Theorems.Thm_lean_workbook_plus_39385
-- name    : lean_workbook_plus_39385
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/96206349-3139-41be-9ea7-d10e8d549490
-- statement:
--   Translating this into a problem where we have 8 slips of paper in a tophat, 2 with each number 1 to 4. The block taken from the tower corresponds to the number removed from the hat. The number of orders to arrange the list $1, 1, 2, 2, 3, 3, 4, 4$ is $\frac{8!}{2!2!2!2!}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39385 :
  8! / (2! * 2! * 2! * 2!) = 90   :=  by sorry
