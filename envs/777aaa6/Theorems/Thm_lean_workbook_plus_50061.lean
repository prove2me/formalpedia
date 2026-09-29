-- Prove2me | Theorems.Thm_lean_workbook_plus_50061
-- name    : lean_workbook_plus_50061
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/a4520b1c-b21e-423a-bb58-34c4fe57c8a4
-- statement:
--   Solution using complementary counting: If we use complementary counting, like the hint above, we are trying to find how we cannot get any pairs. To choose the $4$ pairs out of $5$ pairs that will not be a pair, we calculate $\binom{5}{4}=5$ . Since left and right are distinguishable, we need to multiply on $2^4=16$ , so for the complementary case, we get a total of $5\cdot16=80$ ways. The total number of ways to pick $4$ gloves out of $10$ gloves is just $\binom{10}{4}=210$ , so the answer is $210-80=\boxed{130}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50061 210 - 80 = 130   :=  by sorry
