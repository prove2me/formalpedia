-- Prove2me | Theorems.Thm_lean_workbook_plus_10458
-- name    : lean_workbook_plus_10458
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/15e2012d-3fa4-4739-b790-13db468850a0
-- statement:
--   Prove that if a prime number $p$ divides the product $ab$, then $p$ divides either $a$ or $b$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10458 (p : ℕ) (hp : p.Prime) (a b : ℕ) (hab : p ∣ a * b) : p ∣ a ∨ p ∣ b   :=  by sorry
