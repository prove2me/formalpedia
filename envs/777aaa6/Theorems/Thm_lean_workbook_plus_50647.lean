-- Prove2me | Theorems.Thm_lean_workbook_plus_50647
-- name    : lean_workbook_plus_50647
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/24d28e2a-9fe7-45d1-9986-997b74968430
-- statement:
--   Let $p$ be the probability that $A$ wins if $A$ is up by $1$ point, $q$ be the probability that $A$ wins if the game is tied (what we are looking for), and $r$ be the probability that $A$ wins if $A$ is losing by $1$ point. We have $p=\frac{7}{10}+\frac{3}{10}q$, $q=\frac{7}{10}p+\frac{3}{10}r$, $r=\frac{7}{10}q$. Solving this system yields $q = \boxed{\frac{49}{58}} \approx 84.483\%$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50647  (p q r : ℚ)
  (h₀ : p = 7 / 10 + 3 / 10 * q)
  (h₁ : q = 7 / 10 * p + 3 / 10 * r)
  (h₂ : r = 7 / 10 * q) :
  q = 49 / 58   :=  by sorry
