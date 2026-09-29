-- Prove2me | Theorems.Thm_lean_workbook_plus_16087
-- name    : lean_workbook_plus_16087
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/0a0b2886-7a8a-49d6-a006-075b28da79e7
-- statement:
--   Prove that: $ \gcd \Big( F_m;F_n\Big)=F_{\gcd (m;n)},\forall m,n \in Z^+$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16087 (m n : ℕ) : Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n)   :=  by sorry
