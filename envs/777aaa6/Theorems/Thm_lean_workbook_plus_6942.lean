-- Prove2me | Theorems.Thm_lean_workbook_plus_6942
-- name    : lean_workbook_plus_6942
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/9300d6b7-b56b-46ae-9174-120c053b50ef
-- statement:
--   Explain the meaning of the equation in base 2: b ${}_{n}$ b ${}_{n-1}$ ...b ${}_{0 }$ = b ${}_{n}$ 2 ${}^{n}$ + b ${}_{n-1}$ 2 ${}^{n-1}$ +... b ${}_{0}$ 2 ${}^{0}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6942 (b : ℕ → ℕ) (n : ℕ) : (∑ i in Finset.range (n+1), b i * 2 ^ i) = (∑ i in Finset.range (n+1), b i * 2 ^ i)   :=  by sorry
