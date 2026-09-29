-- Prove2me | Theorems.Thm_lean_workbook_plus_24513
-- name    : lean_workbook_plus_24513
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/35083b0c-e2a8-4f42-beed-b926581536ca
-- statement:
--   Prove that if there exists a rational root of the equation $4x^3 - 3x = p/q$ where $p$ and $q$ are relatively prime integers, then $q$ must have a factor that is a perfect cube (not 1 or -1).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24513 (p q : ℤ) (hq : q ≠ 0) (hpq : Nat.Coprime p.natAbs q.natAbs) : (∃ x : ℚ, 4 * x ^ 3 - 3 * x = p / q) → ∃ y : ℤ, y ^ 3 ∣ q   :=  by sorry
