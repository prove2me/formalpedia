-- Prove2me | Theorems.Thm_lean_workbook_plus_46789
-- name    : lean_workbook_plus_46789
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/9b50fc90-e2c0-44cc-ac46-7c607ea361d9
-- statement:
--   Given $n = p^4q$ with $p, q$ different primes, prove that if $p \mid n$, then either $p^3 \mid p^4$ or $p^3 \mid q$. Conclude that $n$ is a cube.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46789 (n : ℕ) (h : n = p^4 * q) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (h1 : p ∣ n) : p^3 ∣ p^4 ∨ p^3 ∣ q   :=  by sorry
