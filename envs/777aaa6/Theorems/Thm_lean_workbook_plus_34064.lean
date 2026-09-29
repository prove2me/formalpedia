-- Prove2me | Theorems.Thm_lean_workbook_plus_34064
-- name    : lean_workbook_plus_34064
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/7bdbbdb2-d6c9-4269-b7e4-56fbc758bcf4
-- statement:
--   Claim: Let $a,b,c$ be positive integers so that $\gcd(a,b,c)=1$. Then there is an integer $k$ so that $\gcd(a, b+kc)=1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34064 {a b c : ℤ} (habc : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0) (hab : a.gcd b = 1) (hbc : a.gcd c = 1) (hca : b.gcd c = 1) : ∃ k : ℤ, a.gcd (b + k * c) = 1   :=  by sorry
