-- Prove2me | Theorems.Thm_lean_workbook_plus_15734
-- name    : lean_workbook_plus_15734
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/f1b17e4f-47a1-4dbf-b625-b740f15e04b5
-- statement:
--   Prove that if $S(n)$ is the sum of decimal digits of a positive integer $n$, then $S(n) \equiv n \pmod{9}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15734 (n : ℕ) : (Nat.digits 10 n).sum % 9 = n % 9   :=  by sorry
