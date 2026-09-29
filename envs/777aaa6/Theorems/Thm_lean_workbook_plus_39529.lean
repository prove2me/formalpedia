-- Prove2me | Theorems.Thm_lean_workbook_plus_39529
-- name    : lean_workbook_plus_39529
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/68543876-eca2-44c5-9759-4ac5880108ee
-- statement:
--   Let $p, q \in \mathbb{N}$ with $\gcd(p, q) = 1$. Prove that for all $n \in \mathbb{N}$, $\gcd(p^n, q^n) = 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39529 (p q : ℕ) (h : Nat.Coprime p q) (n : ℕ) : Nat.Coprime (p^n) (q^n)   :=  by sorry
