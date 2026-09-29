-- Prove2me | Theorems.Thm_lean_workbook_plus_21402
-- name    : lean_workbook_plus_21402
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/9aead1ed-a740-4757-b35d-5163e184ec07
-- statement:
--   Fibonacci series $ \bmod 29$ is $ 1,1,2,3,5,8,13,21,5,26,2,28,1,0,1,1,...$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21402 : fib 0 ≡ 1 [MOD 29] ∧ fib 1 ≡ 1 [MOD 29] ∧ fib 2 ≡ 2 [MOD 29] ∧ fib 3 ≡ 3 [MOD 29] ∧ fib 4 ≡ 5 [MOD 29] ∧ fib 5 ≡ 8 [MOD 29] ∧ fib 6 ≡ 13 [MOD 29] ∧ fib 7 ≡ 21 [MOD 29] ∧ fib 8 ≡ 5 [MOD 29] ∧ fib 9 ≡ 26 [MOD 29] ∧ fib 10 ≡ 2 [MOD 29] ∧ fib 11 ≡ 28 [MOD 29] ∧ fib 12 ≡ 1 [MOD 29] ∧ fib 13 ≡ 0 [MOD 29] ∧ fib 14 ≡ 1 [MOD 29]   :=  by sorry
