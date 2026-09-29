-- Prove2me | Theorems.Thm_lean_workbook_plus_51287
-- name    : lean_workbook_plus_51287
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/b7a243e0-12d4-4217-8163-0dda4f96ac15
-- statement:
--   Let $F_n$ be a Fibonacci sequence. If $n|m$ , then $F_n|F_m$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51287 (n m : ℕ) (hn : n ∣ m) : fib n ∣ fib m   :=  by sorry
