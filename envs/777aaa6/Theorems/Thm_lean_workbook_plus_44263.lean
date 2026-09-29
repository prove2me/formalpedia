-- Prove2me | Theorems.Thm_lean_workbook_plus_44263
-- name    : lean_workbook_plus_44263
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/70e38b1a-b283-4f9e-a035-6c3dec286738
-- statement:
--   Counting these we get $y=\dbinom{6}{5}+\dbinom{5}{5}+11\left(\dbinom{6}{4}+\dbinom{5}{4}\right)+30\left(\dbinom{6}{3}+\dbinom{5}{3} \right)=1127$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44263 (Nat.choose 6 5 + Nat.choose 5 5 + 11 * (Nat.choose 6 4 + Nat.choose 5 4) + 30 * (Nat.choose 6 3 + Nat.choose 5 3)) = 1127   :=  by sorry
