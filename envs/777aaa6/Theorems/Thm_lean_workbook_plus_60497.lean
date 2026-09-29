-- Prove2me | Theorems.Thm_lean_workbook_plus_60497
-- name    : lean_workbook_plus_60497
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/9fae92ef-124e-4e6e-9cd3-53d2f55e448c
-- statement:
--   Dado que $(n,p)=1$, donde $n, p \in Z^{+}$ y $p$ primo, demostrar que existe un número primo $P_{1}$ y un entero positivo $k$ tal que $nk+p = P_{1}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60497 (n p : ℕ) (hp : p.Prime) (h : Nat.Coprime n p) : ∃ P k : ℕ, P.Prime ∧ n * k + p = P   :=  by sorry
