-- Prove2me | Theorems.Thm_mme_nat_div_real_half_lower
-- name    : mme_nat_div_real_half_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T03:08:21.415505+00:00
-- url     : https://prove2.me/theorems/edc4b344-e48e-4611-ab99-2133ed45bf3c
-- title:
--   A nonzero natural quotient retains half its real value
-- statement:
--   For positive integers $d\le n$, integer division loses at most a factor two compared with real division:
--
--   $$
--   \frac{n}{2d}\le \left\lfloor\frac nd\right\rfloor.
--   $$
--
--   Indeed the quotient is at least one, while the remainder is smaller than $d$. This elementary estimate absorbs the final floor in finite hash-family cardinality bounds.
-- source:
--   Elementary Euclidean-division estimate used to absorb integer rounding in finite combinatorial extraction bounds.

import Mathlib

theorem mme_nat_div_real_half_lower
    {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n) :
    (n : ℝ) / (2 * (d : ℝ)) ≤ ((n / d : ℕ) : ℝ) := by
  sorry
