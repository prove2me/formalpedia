-- Prove2me | Theorems.Thm_lean_workbook_plus_57499
-- name    : lean_workbook_plus_57499
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/510f1b6d-faf3-4760-b171-0fbbba72df67
-- statement:
--   Since the units digit of $5n$ can't be zero, the units digit of $n$ must be odd, and it can't be $1$ , as $1$ is already taken as the rightmost digit. It also can't be $5$ , since that would yield a zero units digit for $2n, 4n, 6n$ . Therefore $n=\overline{1pqrs3}\lor n=\overline{1pqrs7}\lor n=\overline{1pqrs9}$ , where $p,q,r,s$ are some digits.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57499  (n : ℕ)
  (h₀ : 0 < n)
  (h₁ : n % 10 ≠ 0)
  (h₂ : 5 * n % 10 ≠ 0)
  (h₃ : 2 * n % 10 ≠ 0)
  (h₄ : 4 * n % 10 ≠ 0)
  (h₅ : 6 * n % 10 ≠ 0) :
  n % 10 = 1 ∨ n % 10 = 3 ∨ n % 10 = 7 ∨ n % 10 = 9   :=  by sorry
