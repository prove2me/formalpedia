-- Prove2me | Theorems.Thm_lean_workbook_plus_37436
-- name    : lean_workbook_plus_37436
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/09ddd0c4-8431-4185-927b-9e2b6200ea02
-- statement:
--   How does $\phi(25) = 20$ and $\gcd(2, 25) = 1$ relate to the statement that $2^{20} = 1 \mod 5$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37436 :
  (2^20 ≡ 1 [ZMOD 5]) = (Nat.gcd 2 25 = 1 ∧ Nat.totient 25 = 20)   :=  by sorry
