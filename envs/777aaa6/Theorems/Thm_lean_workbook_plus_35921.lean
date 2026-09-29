-- Prove2me | Theorems.Thm_lean_workbook_plus_35921
-- name    : lean_workbook_plus_35921
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/b38a6084-61c8-4fbf-a77a-450a307e0809
-- statement:
--   Let integers $A,B < 10, 000$ be the populations of Acton and Boxborough, respectively. When $A$ is divided by $B$ , the remainder is $1$ . When $B$ is divided by $A$ , the remainder is $2020$ . If the sum of the digits of $A$ is $17$ , find the total combined population of Acton and Boxborough.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35921 (A B : ℕ) (hA : A < 10000) (hB : B < 10000) (hA2 : A % B = 1) (hB2 : B % A = 2020) (hA3 : (Nat.digits 10 A).sum = 17) : A + B = 23120   :=  by sorry
