-- Prove2me | Theorems.Thm_lean_workbook_plus_32376
-- name    : lean_workbook_plus_32376
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/c2c6b963-2509-43c1-8924-a6c9d32fb7a0
-- statement:
--   Prove for all natural numbers $n$ and integer $x\neq1$ , $x^n-1$ is divisible by $x-1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32376 (x : ℤ) (n : ℕ) (hx: x ≠ 1) : x - 1 ∣ x ^ n - 1   :=  by sorry
