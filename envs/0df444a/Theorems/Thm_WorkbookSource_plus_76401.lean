-- Prove2me | Theorems.Thm_WorkbookSource_plus_76401
-- name    : WorkbookSource.plus_76401
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:45:44.10302+00:00
-- url     : https://prove2.me/theorems/bb0b36e8-2847-4c7a-91e5-4d6f120f95dd
-- title:
--   The units digit of a digit-product equation
-- statement:
--   Let $P(n)$ denote the product of the digits of a number, and $S(n)$ denote the sum of the digits of a number. For example, $P(25) = 10$ and $S(25) = 7$ . Suppose $N$ is a two-digit number such that $N = P(N) + S(N).$ What is the units digit of $N$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_76401` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_76401; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_76401 (a b n : ℕ) (h₀ : 1 ≤ a ∧ a ≤ 9) (h₁ : 0 ≤ b ∧ b ≤ 9) (h₂ : n = 10 * a + b) (h₃ : n = a * b + a + b) : b = 9  :=  by sorry
