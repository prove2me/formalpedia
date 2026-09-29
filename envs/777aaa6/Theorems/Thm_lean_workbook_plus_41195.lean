-- Prove2me | Theorems.Thm_lean_workbook_plus_41195
-- name    : lean_workbook_plus_41195
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/62fdbf73-c359-4363-ad01-cfb6184d1302
-- statement:
--   Prove that $\gcd{(F_n,F_m)}=F_{\gcd{(n,m)}}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41195 (n m : ℕ) : Nat.gcd (Nat.fib n) (Nat.fib m) = Nat.fib (Nat.gcd n m)   :=  by sorry
