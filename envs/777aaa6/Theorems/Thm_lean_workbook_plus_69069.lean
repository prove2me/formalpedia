-- Prove2me | Theorems.Thm_lean_workbook_plus_69069
-- name    : lean_workbook_plus_69069
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/5e012bad-a5f1-465c-ac40-ce00d533139e
-- statement:
--   Explanation using inclusion-exclusion: There are $4^6$ ways to assign a number from 1 to 4 to each of the six chocolates. Then by inclusion-exclusion, delete the assignments which omit one of the numbers: $\tbinom43\cdot 3^6$ , add back those which omit two: $\tbinom42\cdot 2^6$ , and again delete those which omit three: $\tbinom41\cdot 1^6$ . The result is $4^6-\tbinom43\cdot 3^6+\tbinom42\cdot 2^6-\tbinom41\cdot 1^6=1560$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69069 4^6 - (Nat.choose 4 3 * 3^6) + (Nat.choose 4 2 * 2^6) - (Nat.choose 4 1 * 1^6) = 1560   :=  by sorry
