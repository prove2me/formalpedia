-- Prove2me | Theorems.Thm_lean_workbook_plus_49464
-- name    : lean_workbook_plus_49464
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/6716e8b7-f133-453b-9208-4eace04688d8
-- statement:
--   Given $n$ positive integers $a_1,a_2,\dotsc ,a_{n}$ each not exceeding $n$, prove that there exists a non-empty subset whose sum of elements is divisible by $n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49464 (n : ℕ) (a : Fin n → ℕ) (ha : ∀ i, a i ≤ n) : ∃ S : Finset (Fin n), (∑ i in S, a i) % n = 0   :=  by sorry
