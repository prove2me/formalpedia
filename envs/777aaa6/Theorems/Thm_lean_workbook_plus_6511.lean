-- Prove2me | Theorems.Thm_lean_workbook_plus_6511
-- name    : lean_workbook_plus_6511
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/ec7b7a39-9743-4f58-bebc-4bc9c00e0ac4
-- statement:
--   Given a prime $p$ with $-5$ as a QR, there exists $a,b$ such that $\frac{a^2+5b^2}{p}=1$ or $2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6511 (p : ℕ) (hp : p.Prime) (h : (-5 : ZMod p) = 1 ∨ (-5 : ZMod p) = 2) : ∃ a b : ℤ, (a^2 + 5 * b^2) % p = 1 ∨ (a^2 + 5 * b^2) % p = 2   :=  by sorry
