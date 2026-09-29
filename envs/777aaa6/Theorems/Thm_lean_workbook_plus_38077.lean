-- Prove2me | Theorems.Thm_lean_workbook_plus_38077
-- name    : lean_workbook_plus_38077
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/42195fa7-22e5-41de-b543-299a1451d596
-- statement:
--   Let the number of pennies be $P$ , the number of nickels be $N$ , and the number of dimes be $D$ . Now, we have two equations: $P+N+D=21$ and $P+5N+10D=100$ . Subtracting the first from the second we obtain: $4N+9D=79 \iff N= \frac{79-9D}{4}$ Now, $N$ must be an integer, so we have $79-9D = 4(19-2D)+(3-D)$ is divisible by $4$ , thus we must have that $3-D$ is divisible by $4$ , which gives $D=3,7,11, \ldots$ . Surely, we can only have either $D=3$ or $D=7$ . Testing, both values of $D$ give solutions: $\boxed{ (P,N,D) = (10,4,7) \text{ or }(P,N,D) = (5,13,3) }$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38077  (p n d : ℕ)
  (h₀ : p + n + d = 21)
  (h₁ : p + 5 * n + 10 * d = 100)
  (h₂ : 0 < p ∧ 0 < n ∧ 0 < d) :
  (p, n, d) = (10, 4, 7) ∨ (p, n, d) = (5, 13, 3)   :=  by sorry
