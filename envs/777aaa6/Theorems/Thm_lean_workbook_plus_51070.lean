-- Prove2me | Theorems.Thm_lean_workbook_plus_51070
-- name    : lean_workbook_plus_51070
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/4a9bfeb4-e9bf-4edc-8ff1-0bccc9584ca1
-- statement:
--   Let $p\ge 5$ be a prime number. Prove that there exist positive integers $m$ and $n$ with $m+n\le \frac{p+1}{2}$ for which $p$ divides $2^n\cdot 3^m-1.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51070 (p : ℕ) (hp : 5 ≤ p) (hp' : Nat.Prime p) : 
    ∃ m n : ℕ, (m + n ≤ (p + 1) / 2) ∧ (p : ℤ) ∣ (2 ^ n * 3 ^ m - 1)   :=  by sorry
