-- Prove2me | Theorems.Thm_lean_workbook_plus_14658
-- name    : lean_workbook_plus_14658
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/473bd8c5-82b8-4d17-bdfa-b79c11a4e725
-- statement:
--   Let's tackle this problem with casework.\n\nFirst of all, we know $k,m,n$ are odd. This means that they are either congruent to 1 or 3 in modulo 4.\n\nCase 1: $k\equiv 1\pmod{4}$. Since $4|k+m$ and $4|m+n$, $m\equiv 3\pmod{4}$, so $n\equiv 1\pmod{4}$. Then adding the two congruences for $k$ and $n$ gives $k+n\equiv 2\pmod{4}$, so $4$ doesn't divide $k+n$ in this case.\n\nCase 2: $k\equiv 3\pmod{4}$. We then get $m\equiv 1\pmod{4}$, so $n\equiv 3\pmod{4}$. Adding both congruences for $k$ and $n$ gives $k+n=6$ so $k+n\equiv 2\pmod{4}$, thus $4$ doesn't divide $k+n$. \n\nIn both cases, $k+n$ isn't divisible by $4$. Therefore we can conclude that $k+n$ is not divisible by $4$, which completes our proof. $\blacksquare$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14658  (k m n : ℤ)
  (h₀ : Odd k ∧ Odd m ∧ Odd n)
  (h₁ : 4 ∣ (k + m))
  (h₂ : 4 ∣ (m + n)) :
  ¬ 4 ∣ (k + n)   :=  by sorry
