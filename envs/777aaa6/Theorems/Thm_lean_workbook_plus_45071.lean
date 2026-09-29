-- Prove2me | Theorems.Thm_lean_workbook_plus_45071
-- name    : lean_workbook_plus_45071
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/e9cd02f9-38db-48f6-9379-cfc550cb15d6
-- statement:
--   First case: permute the numbers 3, 4 and 5. This gives 3! ways. There are 4 spaces in between the digits. Then choose two of them and put in the two '1'. Similarly, there are 6 spaces in between the digits. Then choose two of them and put in the two '2'. So there are $3! \times {4\choose 2} \times {6\choose 2}=540$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45071 3! * (Nat.choose 4 2) * (Nat.choose 6 2) = 540   :=  by sorry
