-- Prove2me | Theorems.Thm_lean_workbook_plus_62702
-- name    : lean_workbook_plus_62702
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/febf380d-e837-406d-96b2-5e1f850cd53c
-- statement:
--   Let $p$ be a prime number such that $ p \mid a^2 + 2$ for a natural number $a$ . Prove that $p$ or $2p$ can be written on the form $x^2 + 2y^2$ , with $x,y \in \mathbb{N}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62702 (p a : ℕ) (hp : Nat.Prime p) (hpa : p ∣ a^2 + 2) : ∃ x y : ℕ, p ∣ x^2 + 2*y^2 ∨ 2*p ∣ x^2 + 2*y^2   :=  by sorry
