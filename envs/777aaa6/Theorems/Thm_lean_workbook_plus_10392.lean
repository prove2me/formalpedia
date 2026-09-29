-- Prove2me | Theorems.Thm_lean_workbook_plus_10392
-- name    : lean_workbook_plus_10392
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/fe355f01-edab-44ce-a509-b058ad41b737
-- statement:
--   There are $\binom 32$ ways to pick two long sleeves and $\binom 31$ ways to pick one short sleeve. The rest of the shirts are automatically grouped. Then there are $2$ ways to give them to the two girls. So the answer is $2\cdot \binom 32 \binom 31 = 2\cdot 3\cdot 3=18$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10392 :
  2 * (Nat.choose 3 2 * Nat.choose 3 1) = 18   :=  by sorry
