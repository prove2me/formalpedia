-- Prove2me | Theorems.Thm_lean_workbook_plus_1001
-- name    : lean_workbook_plus_1001
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/a624ed03-ffa1-4b74-8191-e35dd30f06d7
-- statement:
--   There are $\binom{11}{5} = 462$ ways with no restrictions, but you have to subtract the ones that go through $(2,3)$ . This is $\binom{5}{2}\binom{6}{3} = 200$ , so the answer is $462-200=262$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1001 (Nat.choose 11 5) - (Nat.choose 5 2 * Nat.choose 6 3) = 262   :=  by sorry
