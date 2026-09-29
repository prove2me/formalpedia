-- Prove2me | Theorems.Thm_lean_workbook_plus_76993
-- name    : lean_workbook_plus_76993
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/ba2e686f-d73a-4d60-8adb-aac56fb0eb15
-- statement:
--   There is also a very similar problem (USAMO 03/1) which has the following problem statement: Show that for each $n \in \mathbb{N}$ , we can find an $n$ -digit number with all its digits odd which is divisible by $5^n$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76993 (n : ℕ) : ∃ m, (Nat.digits 10 m).all (Odd ·) ∧ 5^n ∣ m   :=  by sorry
