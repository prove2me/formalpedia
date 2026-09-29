-- Prove2me | Theorems.Thm_lean_workbook_plus_65467
-- name    : lean_workbook_plus_65467
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/1a181d24-37ff-421c-b179-ac5bd3e24c28
-- statement:
--   I've got these things: $f(p-1)=p-1$ for all primes $p$. $f(n)\leq{n}$ for all positive integers.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65467 {f : ℕ → ℕ} (hf : ∀ p, Nat.Prime p → f (p - 1) = p - 1) (hf_le : ∀ n, f n ≤ n) : f 1 = 1   :=  by sorry
