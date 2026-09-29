-- Prove2me | Theorems.Thm_lean_workbook_plus_59577
-- name    : lean_workbook_plus_59577
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/9d02cffd-9f61-4cf4-8cee-3c127284d1f4
-- statement:
--   Prove that Euler's totient function $\phi(n)$ is multiplicative, i.e., $\phi(mn) = \phi(m)\phi(n)$ if $\gcd(m, n) = 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59577 : ∀ m n : ℕ, m ≠ 0 → n ≠ 0 → Nat.Coprime m n → φ (m * n) = φ m * φ n   :=  by sorry
