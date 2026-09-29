-- Prove2me | Theorems.Thm_lean_workbook_plus_38440
-- name    : lean_workbook_plus_38440
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/2d481463-3d65-4eb4-a09e-8453e948da09
-- statement:
--   Prove that $p-1=\Sigma\:\phi(d)$ , where $d\mid p-1$ for all primes $p$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38440 (p : ℕ) (hp : p.Prime) : ∑ k in (Nat.divisors (p-1)), φ k = p-1   :=  by sorry
