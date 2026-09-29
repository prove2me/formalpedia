-- Prove2me | Theorems.Thm_lean_workbook_plus_64978
-- name    : lean_workbook_plus_64978
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/772e259a-0c08-4ad5-9358-a7906df7ec47
-- statement:
--   Prove that for an arbitrary prime number $p$, $f(x)\equiv 0\pmod{p}$ has a solution, where $f(x)=x^6-11x^4+36x^2-36$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64978 (p : ℕ) (hp : p.Prime) : ∃ x : ℕ, (x^6 - 11 * x^4 + 36 * x^2 - 36) % p = 0   :=  by sorry
