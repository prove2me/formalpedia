-- Prove2me | Theorems.Thm_lean_workbook_plus_65780
-- name    : lean_workbook_plus_65780
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/424d816d-d5dc-47de-80a5-6b35005a7251
-- statement:
--   Prove the lemma: $F_{a}| F_{ab}$, where $F_n$ is the $n$-th Fibonacci number and $a, b$ are positive integers.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65780 (a b : ℕ) : fib a ∣ fib (a * b)   :=  by sorry
