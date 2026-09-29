-- Prove2me | Theorems.Thm_lean_workbook_plus_5612
-- name    : lean_workbook_plus_5612
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/73263054-0cbe-4f94-844f-c7d222b7dbba
-- statement:
--   Given positive integers $a,b,n$ such that $\gcd(a,n) = \gcd(b,n) = 1$ . Show these statements: (1): there exist a positive integer $t$ , such that $a^{t}\equiv\ b^{t} \pmod n$ . (2): if $d$ is a smallest positive integer such that $a^{d}\equiv\ b^{d} \pmod n$ , then $d|t$ for any such $t$ . (3): $3^n-2^n$ is not divisible by $ n$ , for any natural number $n>1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5612 (a b n : ℕ) (hab : a ≠ b) (hab2 : a ≠ 0 ∧ b ≠ 0) (hab3 : a * b * n ≠ 0) (hab4 : Nat.gcd a n = 1) (hab5 : Nat.gcd b n = 1) : ∃ t : ℕ, a ^ t ≡ b ^ t [ZMOD n]   :=  by sorry
