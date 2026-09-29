-- Prove2me | Theorems.Thm_lean_workbook_plus_45242
-- name    : lean_workbook_plus_45242
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/62d84472-a8fc-47ea-aebb-b689a3620b46
-- statement:
--   Let $ n$ , $ d$ , and $ q$ represent the number of nickels, dimes, and quarters in the bank, respectively. Then $ n+d+q=100$ and $ 5n+10d+25q=835$ . Also, $ n$ , $ d$ , and $ q$ must be non-negative integers. Dividing the second equation by $ 5$ yields $ n+2d+5q=167$ , and subtracting the first equation from this gives $ d+4q=67$ . Because $ q$ cannot be negative, $ d$ is at most $ 67$ , and we check that $ 67$ dimes and $ 33$ nickels produces $ \$8.35$ . Also, $ d$ cannot be $ 0$ , $ 1$ , or $ 2$ because then $ q$ would not be an integer. Thus, the smallest $ d$ can be is $ 3$ , so $ q=16$ . We can check that $ 16$ quarters, $ 3$ dimes, and $ 81$ nickels works, so the largest $ d$ can be is $ 67$ , and the smallest it can be is $ 3$ , so the difference is $ 64$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45242  (n d q : ℕ)
  (h₀ : 0 < n ∧ 0 < d ∧ 0 < q)
  (h₁ : n + d + q = 100)
  (h₂ : 5 * n + 10 * d + 25 * q = 835) :
  3 ≤ d ∧ d ≤ 67   :=  by sorry
