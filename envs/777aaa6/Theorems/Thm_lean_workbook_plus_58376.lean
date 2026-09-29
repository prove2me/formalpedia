-- Prove2me | Theorems.Thm_lean_workbook_plus_58376
-- name    : lean_workbook_plus_58376
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/72a7949c-f8ed-41f1-8656-1db516043e2d
-- statement:
--   If gcd(a,b) is $1$ then $a$ and $b$ do not share ANY prime divisors. When squaring $a$ and $b$ , the exponents of each prime in the prime factorization are doubled. So, $a^2$ and $b^2$ will still not share any common divisors.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58376  (a b : ℕ)
  (h₀ : Nat.gcd a b = 1) :
  Nat.gcd (a^2) (b^2) = 1   :=  by sorry
