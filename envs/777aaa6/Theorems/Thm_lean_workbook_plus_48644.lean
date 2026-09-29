-- Prove2me | Theorems.Thm_lean_workbook_plus_48644
-- name    : lean_workbook_plus_48644
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/57dd2f7d-a7e8-4094-8ca9-6132a132ffeb
-- statement:
--   We can substitute $x = -1$ to get $p(-1) = (-1+1)\text{stuff} + a - b + c$ . Since $-1+1 = 0$ , the first term is $0$ . We are given that the remainder upon dividing by $x+1$ is $2$ , so we ave $a-b+c = 2$ . Similarly, substituting $x = 4$ gives us $16a + 4b + c = -13$ , and substituting $x = 2$ gives us $4a + 2b + c = 5$ . We now have a system of three equations: $\begin{cases} a - b + c = 2 \\ 16a+4b+c = -13 \\ 4a + 2b + c = 5 \end{cases}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48644  (a b c : ℝ)
  (p : ℝ → ℝ)
  (h₀ : ∀ x, p x = (x + 1) * (x - 4) * (x - 2) + a * x^2 + b * x + c)
  (h₁ : p (-1) = 2)
  (h₂ : p 4 = -13)
  (h₃ : p 2 = 5) :
  a - b + c = 2 ∧ 16 * a + 4 * b + c = -13 ∧ 4 * a + 2 * b + c = 5   :=  by sorry
