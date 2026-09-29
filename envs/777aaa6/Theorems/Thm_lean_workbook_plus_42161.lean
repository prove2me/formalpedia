-- Prove2me | Theorems.Thm_lean_workbook_plus_42161
-- name    : lean_workbook_plus_42161
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/b911eb08-c965-484d-bb1a-40ff186167c4
-- statement:
--   Prove that for all $q\in\mathbb{N}$ with $\gcd(q,10)=1$ , there exists $n\in\mathbb{N}$ such that $q|(10^{n}-1)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42161 (q : ℕ) (hq : Nat.Coprime q 10) : ∃ n : ℕ, q ∣ (10^n - 1)   :=  by sorry
